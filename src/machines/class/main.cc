// The class machine's command line (DESIGN.md §5): a request file in, a .fol.def and a .fol.proof out.
//
//   class_machine REQUEST OUT.fol.def OUT.fol.proof LIB.fol.lib|HEADER.fol.def ...
//
// A request is lines "shape: CLASS|EXACT|VAL|SET", "var: x", "params: p set, Q class, ..." and "formula: ...", the
// formula running to the end of the file. The libraries are the parts its constants and @defs come from.
#include <fstream>
#include <iostream>
#include <sstream>

#include "src/machines/class/ast.h"
#include "src/machines/class/construction.h"
#include "src/parser/parser.h"
#include "src/runtime/runtime.h"

namespace {

std::string trim(const std::string& s) {
    size_t a = s.find_first_not_of(" \t\r\n"), b = s.find_last_not_of(" \t\r\n");
    return a == std::string::npos ? "" : s.substr(a, b - a + 1);
}

// Every @def P(x⃗) <-> body among the loaded axioms.
std::map<std::string, cls::Def> load_defs(logic::Runtime& rt) {
    std::map<std::string, cls::Def> defs;
    for (const auto& [name, sentence] : rt.context().axioms()) {
        try {
            std::vector<std::string> names;
            cls::Fresh fresh("q");
            cls::Ptr f = cls::from_ir(sentence.get().root().get(), names, fresh);
            std::vector<std::string> binders;
            while (f->k == cls::K::Forall) {
                binders.push_back(f->name);
                f = f->a;
            }
            if (f->k != cls::K::Iff || (f->a->k != cls::K::Pred && f->a->k != cls::K::Atom)) continue;
            if (f->a->args != binders || !rt.context().is_defined(f->a->name)) continue;
            if (f->a->k == cls::K::Atom) continue;  // read by a row of its own
            defs[f->a->name] = cls::Def{name, binders, f->b};
        } catch (const cls::Refused&) {
        }
    }
    return defs;
}

}  // namespace

int main(int argc, char* argv[]) {
    if (argc < 4) {
        std::cerr << "usage: class_machine REQUEST OUT.fol.def OUT.fol.proof LIB...\n";
        return 1;
    }
    std::ifstream in(argv[1]);
    std::stringstream ss;
    ss << in.rdbuf();
    std::string text = ss.str();

    cls::Request req;
    std::string shape, formula;
    size_t fpos = text.find("formula:");
    if (fpos == std::string::npos) {
        std::cerr << "request: no formula\n";
        return 1;
    }
    formula = trim(text.substr(fpos + 8));
    std::istringstream head(text.substr(0, fpos));
    for (std::string line; std::getline(head, line);) {
        size_t c = line.find(':');
        if (c == std::string::npos) continue;
        std::string key = trim(line.substr(0, c)), val = trim(line.substr(c + 1));
        if (key == "shape") shape = val;
        if (key == "var") req.var = val;
        if (key == "params") {
            std::istringstream ps(val);
            for (std::string item; std::getline(ps, item, ',');) {
                std::istringstream is(item);
                std::string n, kind;
                is >> n >> kind;
                if (n.empty()) continue;
                if (kind != "set" && kind != "class") {
                    std::cerr << "request: parameter " << n << " is neither set nor class\n";
                    return 1;
                }
                req.params.push_back({n, kind == "set"});
            }
        }
    }
    static const std::map<std::string, cls::Shape> shapes = {
        {"CLASS", cls::Shape::Class}, {"EXACT", cls::Shape::Exact}, {"VAL", cls::Shape::Val}, {"SET", cls::Shape::Set}};
    if (!shapes.count(shape) || req.var.empty()) {
        std::cerr << "request: a shape and a variable are needed\n";
        return 1;
    }
    req.shape = shapes.at(shape);

    logic::Runtime rt;
    for (int i = 4; i < argc; ++i) {
        std::string path = argv[i];
        if (path.size() >= 8 && path.substr(path.size() - 8) == ".fol.lib") {
            auto st = rt.load_library(path);
            if (!st.ok()) {
                std::cerr << "cannot load " << path << ": " << st.error().to_string() << "\n";
                return 1;
            }
        } else {
            auto r = rt.load_file_recursive(path);
            if (!r.ok()) {
                std::cerr << "cannot load " << path << ": " << r.error().to_string() << "\n";
                return 1;
            }
        }
    }

    // The formula, read by the library's parser with its variable and parameters bound in front.
    std::vector<std::string> order = {req.var};
    for (const auto& [n, s] : req.params) order.push_back(n);
    std::string wrapped = "(" + formula + ")";
    for (auto it = order.rbegin(); it != order.rend(); ++it) wrapped = "(forall " + *it + ". " + wrapped + ")";
    std::string err;
    logic::SentenceHandle sh = logic::try_parse_sentence(wrapped, rt.context(), &err);
    if (!sh.valid()) {
        std::cerr << "request: the formula does not parse: " << err << "\n";
        return 1;
    }
    try {
        std::vector<std::string> names;
        cls::Fresh fresh("q");
        cls::Ptr f = cls::from_ir(sh.get().root().get(), names, fresh);
        std::map<std::string, std::string> m;
        for (const auto& n : order) {
            m[f->name] = n;
            f = f->a;
        }
        req.formula = cls::subst(f, m);
        cls::Output out = cls::construct(req, load_defs(rt));
        std::ofstream(argv[2]) << "claim " << out.name << ": " << out.statement << "\n";
        std::ofstream(argv[3]) << out.proof;
        std::cout << out.name << "\n";
    } catch (const cls::Refused& r) {
        std::cerr << "refused: " << r.what() << "\n";
        return 2;
    }
    return 0;
}
