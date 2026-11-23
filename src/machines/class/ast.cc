#include "src/machines/class/ast.h"

namespace cls {

bool is_atom(const std::string& name, size_t arity) {
    static const std::map<std::string, size_t> atoms = {
        {"elem", 2}, {"eq", 2}, {"set", 1}, {"zero", 1}, {"nsucc", 2}, {"snoc", 4}};
    auto it = atoms.find(name);
    return it != atoms.end() && it->second == arity;
}

Ptr atom(const std::string& name, std::vector<std::string> args) {
    K k = is_atom(name, args.size()) ? K::Atom : K::Pred;
    return std::make_shared<const Node>(Node{k, name, std::move(args), nullptr, nullptr});
}

Ptr unary(K k, Ptr a) { return std::make_shared<const Node>(Node{k, "", {}, std::move(a), nullptr}); }

Ptr binary(K k, Ptr a, Ptr b) {
    return std::make_shared<const Node>(Node{k, "", {}, std::move(a), std::move(b)});
}

Ptr quant(K k, const std::string& v, Ptr body) {
    return std::make_shared<const Node>(Node{k, v, {}, std::move(body), nullptr});
}

Ptr from_ir(const logic::Formula& f, std::vector<std::string>& names, Fresh& fresh) {
    if (f.is_predicate()) {
        const auto& p = f.as_predicate();
        std::vector<std::string> args;
        for (const auto& t : p.args()) {
            if (!t.is_generalized()) throw Refused("a fixed variable or a description in an atom");
            size_t k = t.as_variable();
            if (k >= names.size()) throw Refused("a variable bound nowhere");
            args.push_back(names[names.size() - 1 - k]);
        }
        return atom(p.predicate().get().get_name(), std::move(args));
    }
    if (f.is_compound()) {
        const auto& c = f.as_compound();
        switch (c.op) {
            case logic::Op::Bottom: return std::make_shared<const Node>(Node{K::False, "", {}, nullptr, nullptr});
            case logic::Op::Not: return unary(K::Not, from_ir(c.left.get(), names, fresh));
            case logic::Op::And: return binary(K::And, from_ir(c.left.get(), names, fresh), from_ir(c.right.get(), names, fresh));
            case logic::Op::Or: return binary(K::Or, from_ir(c.left.get(), names, fresh), from_ir(c.right.get(), names, fresh));
            case logic::Op::Implies: return binary(K::Imp, from_ir(c.left.get(), names, fresh), from_ir(c.right.get(), names, fresh));
            case logic::Op::Iff: return binary(K::Iff, from_ir(c.left.get(), names, fresh), from_ir(c.right.get(), names, fresh));
            default: throw Refused("an unknown connective");
        }
    }
    if (f.is_quantified()) {
        const auto& q = f.as_quantified();
        std::string v = fresh();
        names.push_back(v);
        Ptr body = from_ir(q.body.get(), names, fresh);
        names.pop_back();
        return quant(q.op == logic::Op::Forall ? K::Forall : K::Exists, v, body);
    }
    if (f.is_sentence()) return from_ir(f.as_sentence().get().root().get(), names, fresh);
    throw Refused("a schema variable");
}

Ptr guard(const Ptr& f) {
    switch (f->k) {
        case K::Forall:
        case K::Exists: {
            K want = f->k == K::Forall ? K::Imp : K::And;
            const Ptr& b = f->a;
            if (b->k == want && b->a->k == K::Atom && b->a->name == "set" && b->a->args[0] == f->name)
                return quant(f->k == K::Forall ? K::All : K::Ex, f->name, guard(b->b));
            throw Refused("a quantifier without its set guard: " + print(f));
        }
        case K::Not: return unary(K::Not, guard(f->a));
        case K::And:
        case K::Or:
        case K::Imp:
        case K::Iff: return binary(f->k, guard(f->a), guard(f->b));
        case K::All:
        case K::Ex: return quant(f->k, f->name, guard(f->a));
        default: return f;
    }
}

namespace {

std::vector<std::string> map_args(const std::vector<std::string>& args, const std::map<std::string, std::string>& m) {
    std::vector<std::string> out;
    for (const auto& a : args) {
        auto it = m.find(a);
        out.push_back(it == m.end() ? a : it->second);
    }
    return out;
}

}  // namespace

Ptr rename(const Ptr& f, const std::map<std::string, std::string>& m, Fresh& fresh) {
    switch (f->k) {
        case K::Atom:
        case K::Pred: return atom(f->name, map_args(f->args, m));
        case K::False: return f;
        case K::Not: return unary(K::Not, rename(f->a, m, fresh));
        case K::And:
        case K::Or:
        case K::Imp:
        case K::Iff: return binary(f->k, rename(f->a, m, fresh), rename(f->b, m, fresh));
        default: {
            std::string v = fresh();
            auto m2 = m;
            m2[f->name] = v;
            return quant(f->k, v, rename(f->a, m2, fresh));
        }
    }
}

Ptr subst(const Ptr& f, const std::map<std::string, std::string>& m) {
    switch (f->k) {
        case K::Atom:
        case K::Pred: return atom(f->name, map_args(f->args, m));
        case K::False: return f;
        case K::Not: return unary(K::Not, subst(f->a, m));
        case K::And:
        case K::Or:
        case K::Imp:
        case K::Iff: return binary(f->k, subst(f->a, m), subst(f->b, m));
        default: {
            auto m2 = m;
            m2.erase(f->name);
            return quant(f->k, f->name, subst(f->a, m2));
        }
    }
}

std::string print(const Ptr& f) {
    switch (f->k) {
        case K::Atom:
        case K::Pred: {
            std::string s = f->name + "(";
            for (size_t i = 0; i < f->args.size(); ++i) s += (i ? ", " : "") + f->args[i];
            return s + ")";
        }
        case K::False: return "false";
        case K::Not: return "(~ " + print(f->a) + ")";
        case K::And: return "(" + print(f->a) + " & " + print(f->b) + ")";
        case K::Or: return "(" + print(f->a) + " | " + print(f->b) + ")";
        case K::Imp: return "(" + print(f->a) + " -> " + print(f->b) + ")";
        case K::Iff: return "(" + print(f->a) + " <-> " + print(f->b) + ")";
        case K::All: return "(forall " + f->name + ". (set(" + f->name + ") -> " + print(f->a) + "))";
        case K::Ex: return "(exists " + f->name + ". (set(" + f->name + ") & " + print(f->a) + "))";
        case K::Forall: return "(forall " + f->name + ". " + print(f->a) + ")";
        case K::Exists: return "(exists " + f->name + ". " + print(f->a) + ")";
    }
    return "";
}

}  // namespace cls
