#include "src/machines/compress/compress.h"

#include <algorithm>
#include <cctype>
#include <iterator>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/stack.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/translate/pass.h"

namespace logic::compress {
namespace {

namespace nd = proof::nd;
using proof::NDProgram;
using proof::translate::overloaded;

// ---- printing: formula.y's grammar, with the parentheses it needs and no space it does not ----

bool keyword(const std::string& s) {
    static const std::unordered_set<std::string> words = {
        "forall", "exists", "and", "or", "not", "implies", "iff", "false", "bottom", "axiom", "claim", "theorem",
        "proof", "fix", "assume", "let", "qed", "use", "and_intro", "and_elim_l", "and_elim_r", "or_intro_l",
        "or_intro_r", "or_elim", "implies_intro", "implies_elim", "not_intro", "not_elim", "bottom_elim",
        "iff_intro", "iff_elim_l", "iff_elim_r", "forall_intro", "forall_elim", "exists_intro", "exists_elim",
        "double_neg_elim", "excluded_middle", "peirce", "classical_absurd", "eq_sym", "iota_elim", "iota",
        "include", "UNPROVED", "schema", "schema_inst"};
    return words.count(s) > 0;
}

bool identifier(const std::string& s) {
    auto word = [](char c) { return std::isalnum(static_cast<unsigned char>(c)) || c == '_'; };
    if (s.empty() || std::isdigit(static_cast<unsigned char>(s[0])) || !word(s[0])) return false;
    size_t i = 1;
    while (i < s.size() && word(s[i])) ++i;
    while (i < s.size() && s[i] == '\'') ++i;
    return i == s.size() && !keyword(s);
}

std::string qualified(const std::string& name) {
    std::string out;
    for (size_t start = 0, n = 0;; ++n) {
        size_t dot = name.find('.', start);
        std::string seg = name.substr(start, dot == std::string::npos ? std::string::npos : dot - start);
        bool digits = !seg.empty() && std::all_of(seg.begin(), seg.end(), [](char c) { return std::isdigit(static_cast<unsigned char>(c)) != 0; });
        if (n) out += '.';
        out += identifier(seg) || (n && digits) ? seg : '"' + seg + '"';
        if (dot == std::string::npos) return out;
        start = dot + 1;
    }
}

enum Prec { kIff = 1, kImplies, kOr, kAnd, kUnary };

std::string spelling(size_t j) {
    static const std::string first = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    static const std::string rest = first + "0123456789_";
    std::string s(1, first[j % first.size()]);
    for (j /= first.size(); j > 0; j = (j - 1) / rest.size()) s += rest[(j - 1) % rest.size()];
    return s;
}

void free_names(const ASTNode* n, std::vector<std::string>& bound, std::vector<std::string>& out) {
    if (!n) return;
    switch (n->type) {
        case ASTNode::Forall:
        case ASTNode::Exists:
        case ASTNode::DescriptionTerm:
            bound.push_back(n->name);
            free_names(n->body, bound, out);
            bound.pop_back();
            return;
        case ASTNode::Term:
            if (std::find(bound.begin(), bound.end(), n->name) == bound.end()) out.push_back(n->name);
            return;
        case ASTNode::Predicate:
            if (n->args)
                for (const ASTNode* a : *n->args) free_names(a, bound, out);
            return;
        default:
            free_names(n->left, bound, out);
            free_names(n->right, bound, out);
    }
}

std::vector<std::string> free_names(const ParsedProofStep& s) {
    std::vector<std::string> out, bound;
    free_names(s.formula_ast.get(), bound, out);
    for (const auto& b : s.schema_bindings) {
        bound = b.lambda_params;
        free_names(b.formula_ast.get(), bound, out);
    }
    return out;
}

// Prints blocks in formula.y's grammar, with the parentheses it needs and no space it does not. Given `terms`, it writes
// the names fix, exists_elim and iota_elim bind as `terms` maps them, and each bound variable by its depth: the checker
// reads neither name, a bound variable being its position and a fixed one the step that binds it.
class Printer {
public:
    explicit Printer(const std::unordered_map<std::string, std::string>* terms = nullptr) : terms_(terms) {}

    std::string block(const ParsedProof& p) {
        using K = ParsedProofStep::Kind;
        std::string o = "proof " + qualified(p.claim_name) + ":";
        if (p.unproved) {
            o += " UNPROVED";
            for (const auto& s : p.steps) o += " use " + qualified(s.rule_name);
            return o + "\n";
        }
        for (const auto& s : p.steps) {
            o += '\n';
            switch (s.kind) {
                case K::Fix:
                    o += "fix " + s.args[0];
                    break;
                case K::Assume:
                case K::Let:
                    o += s.result_name + (s.kind == K::Assume ? "=assume " : "=let ");
                    whole(o, s.formula_ast.get(), {});
                    break;
                case K::Use:
                    o += s.result_name + "=use " + qualified(s.rule_name);
                    break;
                case K::Rule:
                    o += s.result_name + "=" + s.rule_name + " ";
                    for (size_t i = 0; i < s.args.size(); ++i) o += (i ? "," : "") + s.args[i];
                    break;
                case K::SchemaInst:
                    o += s.result_name + "=schema_inst " + qualified(s.rule_name) + "{";
                    for (size_t i = 0; i < s.schema_bindings.size(); ++i) {
                        const auto& b = s.schema_bindings[i];
                        o += (i ? "," : "") + b.var_name + ":";
                        whole(o, b.formula_ast.get(), b.lambda_params);
                    }
                    o += '}';
                    break;
                case K::Qed:
                    o += "qed " + s.args[0];
                    break;
            }
        }
        return o + "\n";
    }

private:
    const std::unordered_map<std::string, std::string>* terms_;
    std::vector<std::pair<std::string, std::string>> bound_;  // the variables bound here, innermost last, as written
    std::vector<std::string> depth_;                         // the name a variable bound at each depth is written
    std::unordered_set<std::string> avoid_;                   // the names the formula reads free, as written
    size_t next_ = 0;

    std::string free_name(const std::string& n) const {
        if (terms_)
            if (auto it = terms_->find(n); it != terms_->end()) return it->second;
        return n;
    }

    void push(const std::string& n) {
        if (!terms_) {
            bound_.emplace_back(n, n);
            return;
        }
        while (depth_.size() <= bound_.size()) {
            std::string s;
            do s = spelling(next_++);
            while (keyword(s) || avoid_.count(s));
            depth_.push_back(s);
        }
        bound_.emplace_back(n, depth_[bound_.size()]);
    }

    // A step's formula, or a schema binding's with its lambda parameters bound first.
    void whole(std::string& o, const ASTNode* n, const std::vector<std::string>& params) {
        bound_.clear();
        depth_.clear();
        avoid_.clear();
        next_ = 0;
        if (terms_) {
            std::vector<std::string> names, b = params;
            free_names(n, b, names);
            for (const auto& x : names) avoid_.insert(free_name(x));
        }
        for (const auto& x : params) push(x);
        if (!params.empty()) {
            o += '\\';
            for (size_t j = 0; j < bound_.size(); ++j) o += (j ? " " : "") + bound_[j].second;
            o += '.';
        }
        formula(o, n, kIff, true);
    }

    void term(std::string& o, const ASTNode* n) {
        if (n->type != ASTNode::DescriptionTerm) {
            auto b = std::find_if(bound_.rbegin(), bound_.rend(), [&](const auto& v) { return v.first == n->name; });
            o += b != bound_.rend() ? b->second : free_name(n->name);
            return;
        }
        push(n->name);
        o += "(iota " + bound_.back().second + ".";
        formula(o, n->body, kIff, true);
        o += ')';
        bound_.pop_back();
    }

    // `last`: nothing follows before the enclosing parenthesis closes, so a quantifier, whose body runs as far as it
    // can, stands bare.
    void formula(std::string& o, const ASTNode* n, int min, bool last) {
        switch (n->type) {
            case ASTNode::And:
            case ASTNode::Or:
            case ASTNode::Implies:
            case ASTNode::Iff: {
                int p = n->type == ASTNode::And   ? kAnd
                        : n->type == ASTNode::Or  ? kOr
                        : n->type == ASTNode::Iff ? kIff
                                                  : kImplies;
                bool paren = p < min, right = p == kImplies;
                if (paren) o += '(';
                formula(o, n->left, right ? p + 1 : p, false);
                o += p == kAnd ? "&" : p == kOr ? "|" : right ? "->" : "<->";
                formula(o, n->right, right ? p : p + 1, paren || last);
                if (paren) o += ')';
                return;
            }
            case ASTNode::Not:
                o += '~';
                formula(o, n->left, kUnary, last);
                return;
            case ASTNode::Forall:
            case ASTNode::Exists:
                if (!last) o += '(';
                push(n->name);
                o += (n->type == ASTNode::Forall ? "forall " : "exists ") + bound_.back().second + ".";
                formula(o, n->body, kIff, true);
                bound_.pop_back();
                if (!last) o += ')';
                return;
            case ASTNode::Bottom:
                o += "_|_";
                return;
            case ASTNode::Predicate:
                o += qualified(n->name);
                if (n->args && !n->args->empty()) {
                    o += '(';
                    for (size_t i = 0; i < n->args->size(); ++i) {
                        if (i) o += ',';
                        term(o, (*n->args)[i]);
                    }
                    o += ')';
                }
                return;
            default:
                throw std::logic_error("compress: a formula holds a node no formula holds");
        }
    }
};

// ---- what each step reads ----

// A step read by a later one: as a held fact (`held`: the rule needs it derived and reads the scopes it rests on), or as
// a bare formula (or_intro's other side, bottom_elim's target, excluded_middle's and peirce's formulas).
struct Cite {
    size_t arg;
    uint32_t step;
    bool held;
};

struct Reads {
    std::vector<Cite> cites;
    std::vector<uint32_t> terms;
};

Reads reads(const nd::Instr& in) {
    auto h = [](size_t a, proof::StepRef r) { return Cite{a, r.idx, true}; };
    auto f = [](size_t a, proof::StepRef r) { return Cite{a, r.idx, false}; };
    auto one = [&](proof::StepRef r) { return Reads{{h(0, r)}, {}}; };
    auto two = [&](proof::StepRef a, proof::StepRef b) { return Reads{{h(0, a), h(1, b)}, {}}; };
    return std::visit(
        overloaded{
            [](const nd::Fix&) { return Reads{}; },
            [](const nd::Assume&) { return Reads{}; },
            [](const nd::Let&) { return Reads{}; },
            [](const nd::Use&) { return Reads{}; },
            [](const nd::SchemaInst&) { return Reads{}; },
            [&](const nd::AndIntro& o) { return two(o.a, o.b); },
            [&](const nd::AndElimL& o) { return one(o.of); },
            [&](const nd::AndElimR& o) { return one(o.of); },
            [&](const nd::OrIntroL& o) { return Reads{{h(0, o.a), f(1, o.b_formula)}, {}}; },
            [&](const nd::OrIntroR& o) { return Reads{{f(0, o.a_formula), h(1, o.b)}, {}}; },
            [&](const nd::OrElim& o) { return Reads{{h(0, o.or_formula), h(1, o.ac), h(2, o.bc)}, {}}; },
            [&](const nd::ImpliesIntro& o) { return one(o.conclusion); },
            [&](const nd::ImpliesElim& o) { return two(o.impl, o.ant); },
            [&](const nd::NotIntro& o) { return one(o.bottom); },
            [&](const nd::NotElim& o) { return two(o.negation, o.formula); },
            [&](const nd::BottomElim& o) { return Reads{{h(0, o.bottom), f(1, o.target_formula)}, {}}; },
            [&](const nd::IffIntro& o) { return two(o.ab, o.ba); },
            [&](const nd::IffElimL& o) { return two(o.iff, o.a); },
            [&](const nd::IffElimR& o) { return two(o.iff, o.b); },
            [&](const nd::ForallIntro& o) { return one(o.body); },
            [&](const nd::ForallElim& o) { return Reads{{h(0, o.formula)}, {o.term.idx}}; },
            [&](const nd::ExistsIntro& o) {
                Reads r = one(o.body);
                if (o.witness) r.terms.push_back(o.witness->idx);
                return r;
            },
            [&](const nd::ExistsElim& o) { return one(o.formula); },
            [&](const nd::EqSym& o) { return one(o.eq_formula); },
            [&](const nd::DoubleNegElim& o) { return one(o.of); },
            [&](const nd::ExcludedMiddle& o) { return Reads{{f(0, o.formula_let)}, {}}; },
            [&](const nd::ClassicalAbsurd& o) { return one(o.bottom); },
            [&](const nd::Peirce& o) { return Reads{{f(0, o.a_let), f(1, o.b_let)}, {}}; },
            [&](const nd::IotaElim& o) { return one(o.exists_formula); },
            [&](const nd::Qed& o) { return one(o.derived); },
        },
        in);
}

bool opens(const nd::Instr& in) {
    return std::holds_alternative<nd::Fix>(in) || std::holds_alternative<nd::Assume>(in) ||
           std::holds_alternative<nd::ExistsElim>(in);
}

bool closes(const nd::Instr& in) {
    if (const auto* e = std::get_if<nd::ExistsIntro>(&in)) return !e->witness;
    return std::holds_alternative<nd::ImpliesIntro>(in) || std::holds_alternative<nd::NotIntro>(in) ||
           std::holds_alternative<nd::ClassicalAbsurd>(in) || std::holds_alternative<nd::ForallIntro>(in);
}

bool names_step(const nd::Instr& in) { return !std::holds_alternative<nd::Fix>(in) && !std::holds_alternative<nd::Qed>(in); }

// The name later formulas read a step's term by.
const proof::ScopeName* binds_name(const nd::Instr& in) {
    if (const auto* f = std::get_if<nd::Fix>(&in)) return &f->var_name;
    if (const auto* e = std::get_if<nd::ExistsElim>(&in)) return e->bind_witness ? &*e->bind_witness : nullptr;
    if (const auto* t = std::get_if<nd::IotaElim>(&in)) return t->bind_iota ? &*t->bind_iota : nullptr;
    return nullptr;
}

// ---- the replay: the checker's own stack, run on the trace's formulas, says which step set each held fact ----

class Probe : public ClassicalProofStack {
public:
    using ClassicalProofStack::ClassicalProofStack;
    void derive(FormulaHandle f, const ScopeDeps& d) { derive_with_deps(f, d); }
    ScopeDeps var_deps(FormulaHandle f) const { return compute_var_deps(f); }
    int scope_of(const Term& t) const { return find_scope_for_term(t); }
};

util::ResultStatus replay(Probe& p, const nd::Instr& in, const nd::NDVerifier::TraceFull& t, const ScopeDeps& names,
                          uint32_t i) {
    const auto& env = t.step_env;
    auto same = [&](const FormulaResult& r) -> util::ResultStatus {
        if (!r.ok()) return r.error();
        if (r.value() != env[i]) return MAKE_ERROR << "step " << i << ": the replay derives another formula";
        return util::Ok();
    };
    auto term = [&](uint32_t k) { return t.term_env[k]; };
    auto bound = [&](const std::optional<Term>& v) -> util::ResultStatus {
        if (!v || !(*v == t.term_env[i])) return MAKE_ERROR << "step " << i << ": the replay binds another term";
        return util::Ok();
    };
    using R = util::ResultStatus;
    return std::visit(
        overloaded{
            [&](const nd::Fix&) -> R { return bound(p.fix_var()); },
            [&](const nd::Assume&) -> R {
                p.assume(env[i]);
                return util::Ok();
            },
            [&](const nd::Let&) -> R { return util::Ok(); },
            [&](const nd::Use& o) -> R {
                SentenceHandle s = o.axiom.sentence;
                return same(p.use_theorem(s));
            },
            [&](const nd::SchemaInst&) -> R {
                p.derive(env[i], names);
                return util::Ok();
            },
            [&](const nd::AndIntro& o) -> R { return same(p.and_intro(env[o.a.idx], env[o.b.idx])); },
            [&](const nd::AndElimL& o) -> R { return same(p.and_elim_l(env[o.of.idx])); },
            [&](const nd::AndElimR& o) -> R { return same(p.and_elim_r(env[o.of.idx])); },
            [&](const nd::OrIntroL& o) -> R { return same(p.or_intro_l(env[o.a.idx], env[o.b_formula.idx])); },
            [&](const nd::OrIntroR& o) -> R { return same(p.or_intro_r(env[o.a_formula.idx], env[o.b.idx])); },
            [&](const nd::OrElim& o) -> R {
                return same(p.or_elim(env[o.or_formula.idx], env[o.ac.idx], env[o.bc.idx]));
            },
            [&](const nd::ImpliesIntro& o) -> R { return same(p.implies_intro(env[o.conclusion.idx])); },
            [&](const nd::ImpliesElim& o) -> R { return same(p.implies_elim(env[o.impl.idx], env[o.ant.idx])); },
            [&](const nd::NotIntro& o) -> R { return same(p.not_intro(env[o.bottom.idx])); },
            [&](const nd::NotElim& o) -> R { return same(p.not_elim(env[o.negation.idx], env[o.formula.idx])); },
            [&](const nd::BottomElim& o) -> R {
                return same(p.bottom_elim(env[o.bottom.idx], env[o.target_formula.idx]));
            },
            [&](const nd::IffIntro& o) -> R { return same(p.iff_intro(env[o.ab.idx], env[o.ba.idx])); },
            [&](const nd::IffElimL& o) -> R { return same(p.iff_elim_l(env[o.iff.idx], env[o.a.idx])); },
            [&](const nd::IffElimR& o) -> R { return same(p.iff_elim_r(env[o.iff.idx], env[o.b.idx])); },
            [&](const nd::ForallIntro& o) -> R { return same(p.forall_intro(env[o.body.idx])); },
            [&](const nd::ForallElim& o) -> R { return same(p.forall_elim(env[o.formula.idx], term(o.term.idx))); },
            [&](const nd::ExistsIntro& o) -> R {
                std::optional<Term> w;
                if (o.witness) w = term(o.witness->idx);
                return same(p.exists_intro(env[o.body.idx], w));
            },
            [&](const nd::ExistsElim& o) -> R {
                TRY(same(p.exists_elim(env[o.formula.idx])));
                return o.bind_witness ? bound(p.last_witness_var()) : util::Ok();
            },
            [&](const nd::EqSym& o) -> R { return same(p.eq_sym(env[o.eq_formula.idx])); },
            [&](const nd::DoubleNegElim& o) -> R { return same(p.double_neg_elim(env[o.of.idx])); },
            [&](const nd::ExcludedMiddle& o) -> R { return same(p.excluded_middle(env[o.formula_let.idx])); },
            [&](const nd::ClassicalAbsurd& o) -> R { return same(p.classical_absurd(env[o.bottom.idx])); },
            [&](const nd::Peirce& o) -> R { return same(p.peirce(env[o.a_let.idx], env[o.b_let.idx])); },
            [&](const nd::IotaElim& o) -> R {
                TRY(same(p.iota_elim(env[o.exists_formula.idx])));
                return o.bind_iota ? bound(p.last_iota_term()) : util::Ok();
            },
            [&](const nd::Qed&) -> R { return util::Ok(); },
        },
        in);
}

// Per step up to the qed: the step each citation is read from, what else it needs kept, and its scope.
struct Plan {
    uint32_t n = 0;
    std::vector<std::vector<Cite>> cites;
    std::vector<std::vector<uint32_t>> from;
    std::vector<std::vector<uint32_t>> needs;  // the steps binding the terms and names it reads
    std::vector<int> parent;                   // the opener of the innermost scope it sits in
    std::vector<int> closer;                   // an opener's closer
};

util::Result<Plan> plan(GlobalContext& ctx, const ParsedProof& p, const NDProgram& prog) {
    nd::NDVerifier verifier;
    TRY_ASSIGN(t, verifier.trace_full(ctx, prog));
    const auto& env = t.step_env;
    Probe probe(ctx);
    std::unordered_map<FormulaHandle, uint32_t> owner;  // the step that set each held fact's entry
    std::unordered_map<std::string, Term> terms;        // the verifier's name table
    std::unordered_map<std::string, uint32_t> binder;
    std::vector<uint32_t> open;
    const auto size = prog.instrs.size();
    Plan plan;
    plan.cites.resize(size);
    plan.from.resize(size);
    plan.needs.resize(size);
    plan.parent.assign(size, -1);
    plan.closer.assign(size, -1);
    for (uint32_t i = 0; i < size; ++i) {
        const nd::Instr& in = prog.instrs[i];
        Reads r = reads(in);
        for (const Cite& c : r.cites) {
            FormulaHandle f = env[c.step];
            bool held = probe.derived().count(f) > 0;
            if (c.held && !held) return MAKE_ERROR << "step " << i << " reads a fact not held";
            plan.from[i].push_back(held ? owner.at(f) : c.step);
        }
        plan.cites[i] = std::move(r.cites);
        plan.needs[i] = std::move(r.terms);
        ScopeDeps names;
        for (const auto& name : free_names(p.steps[i])) {
            if (auto b = binder.find(name); b != binder.end()) plan.needs[i].push_back(b->second);
            auto tm = terms.find(name);
            if (tm == terms.end()) continue;
            if (tm->second.is_fixed()) {
                if (int s = probe.scope_of(tm->second); s >= 0) names.set(s);
            } else if (tm->second.is_description()) {
                names |= probe.var_deps(tm->second.as_description().body);
            }
        }
        if (!open.empty()) plan.parent[i] = static_cast<int>(open.back());
        bool derives = names_step(in) && !std::holds_alternative<nd::Let>(in);
        auto before = derives ? probe.derived().find(env[i]) : probe.derived().end();
        bool had = before != probe.derived().end();
        int depth = had ? before->second.deepest() : 0;
        TRY(replay(probe, in, t, names, i));
        if (derives) {
            auto after = probe.derived().find(env[i]);
            if (after != probe.derived().end() && (!had || after->second.deepest() != depth)) owner[env[i]] = i;
        }
        if (closes(in)) {
            plan.closer[open.back()] = static_cast<int>(i);
            open.pop_back();
        }
        if (opens(in)) open.push_back(i);
        if (const auto* name = binds_name(in)) {
            terms[name->name] = t.term_env[i];
            binder[name->name] = i;
        }
        if (std::holds_alternative<nd::Qed>(in)) {
            plan.n = i + 1;
            return plan;
        }
    }
    return MAKE_ERROR << "no qed";
}

// Kept: the qed, and every step a kept step reads, binds a term or name for, or sits in the scope of.
std::vector<char> kept(const Plan& plan, uint32_t qed) {
    std::vector<char> keep(plan.n, 0);
    std::vector<uint32_t> work;
    auto mark = [&](int k) {
        if (k >= 0 && !keep[k]) {
            keep[k] = 1;
            work.push_back(static_cast<uint32_t>(k));
        }
    };
    mark(static_cast<int>(qed));
    while (!work.empty()) {
        uint32_t i = work.back();
        work.pop_back();
        for (uint32_t k : plan.from[i]) mark(static_cast<int>(k));
        for (uint32_t k : plan.needs[i]) mark(static_cast<int>(k));
        mark(plan.parent[i]);
        mark(plan.closer[i]);
    }
    return keep;
}

// A name per kept step, reused once the step it named is read no more; the most-read steps take the shortest. The names
// terms take start with '_', which no step's does: lowering binds a name `fix` binds as a step name too.
std::vector<std::string> names(const Plan& plan, const std::vector<char>& keep, const NDProgram& prog) {
    std::vector<std::string> spellings;
    auto spell = [&](size_t j) -> const std::string& {
        while (spellings.size() <= j) spellings.push_back(spelling(spellings.size()));
        return spellings[j];
    };
    std::vector<uint32_t> last(plan.n), count(plan.n, 0), order;
    for (uint32_t i = 0; i < plan.n; ++i) last[i] = i;
    for (uint32_t i = 0; i < plan.n; ++i)
        if (keep[i])
            for (uint32_t k : plan.from[i]) {
                last[k] = std::max(last[k], i);
                ++count[k];
            }
    for (uint32_t i = 0; i < plan.n; ++i)
        if (keep[i] && names_step(prog.instrs[i])) order.push_back(i);
    std::stable_sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) { return count[a] > count[b]; });
    std::vector<std::map<uint32_t, uint32_t>> taken;  // per spelling: its steps, each to its last read
    std::vector<std::string> out(plan.n);
    for (uint32_t k : order) {
        for (size_t j = 0;; ++j) {
            if (j == taken.size()) taken.emplace_back();
            const std::string& s = spell(j);
            if (keyword(s)) continue;
            auto& t = taken[j];
            auto next = t.upper_bound(k);
            if (next != t.end() && next->first < last[k]) continue;
            if (next != t.begin() && std::prev(next)->second > k) continue;
            t.emplace(k, last[k]);
            out[k] = s;
            break;
        }
    }
    return out;
}

struct Rewrite {
    ParsedProof proof;
    std::unordered_map<std::string, std::string> terms;  // each name a kept step binds for a term, and its new name
};

std::optional<Rewrite> rewrite(GlobalContext& ctx, const ParsedProof& p) {
    using K = ParsedProofStep::Kind;
    auto lowered = nd::lower(p, ctx);
    if (!lowered.ok()) return std::nullopt;
    const NDProgram& prog = lowered.value();
    auto planned = plan(ctx, p, prog);
    if (!planned.ok()) return std::nullopt;
    const Plan& pl = planned.value();
    std::vector<char> keep = kept(pl, pl.n - 1);
    std::vector<std::string> name = names(pl, keep, prog);
    // A term argument: an argument of a rule no citation names.
    auto term_args = [&](uint32_t i) {
        std::vector<size_t> out;
        if (p.steps[i].kind == K::Fix) out.push_back(0);
        if (p.steps[i].kind != K::Rule) return out;
        std::vector<char> cited(p.steps[i].args.size(), 0);
        for (const Cite& c : pl.cites[i]) cited[c.arg] = 1;
        for (size_t k = 0; k < cited.size(); ++k)
            if (!cited[k]) out.push_back(k);
        return out;
    };
    Rewrite r;
    std::unordered_map<std::string, size_t> reads;
    std::vector<std::string> order;
    for (uint32_t i = 0; i < pl.n; ++i)
        if (const auto* b = binds_name(prog.instrs[i]); keep[i] && b && !reads.count(b->name)) {
            reads[b->name] = 0;
            order.push_back(b->name);
        }
    for (uint32_t i = 0; i < pl.n; ++i) {
        if (!keep[i]) continue;
        std::vector<std::string> read = free_names(p.steps[i]);
        for (size_t k : term_args(i)) read.push_back(p.steps[i].args[k]);
        for (const auto& n : read)
            if (auto it = reads.find(n); it != reads.end()) ++it->second;
    }
    std::stable_sort(order.begin(), order.end(), [&](const auto& a, const auto& b) { return reads[a] > reads[b]; });
    for (size_t j = 0; j < order.size(); ++j) r.terms[order[j]] = "_" + spelling(j);
    r.proof.claim_name = p.claim_name;
    for (uint32_t i = 0; i < pl.n; ++i) {
        if (!keep[i]) continue;
        ParsedProofStep s = p.steps[i];
        for (size_t k : term_args(i))
            if (auto it = r.terms.find(s.args[k]); it != r.terms.end()) s.args[k] = it->second;
        for (size_t c = 0; c < pl.cites[i].size(); ++c) s.args[pl.cites[i][c].arg] = name[pl.from[i][c]];
        s.result_name = names_step(prog.instrs[i]) ? name[i] : s.kind == K::Fix ? s.args[0] : s.result_name;
        r.proof.steps.push_back(std::move(s));
    }
    return r;
}

// The block's text parsed back and run as proof_checker runs it; on success its claim is registered.
bool runs(Runtime& rt, const std::string& text) {
    try {
        std::string error;
        ParseResult parsed = try_parse_with_proofs(text, rt.context(), &error);
        return error.empty() && parsed.proofs.size() == 1 && rt.execute_proof(parsed.proofs[0]).ok();
    } catch (const std::exception&) {
        return false;
    }
}

}  // namespace

util::ResultStatus compress(Runtime& rt, std::FILE* in, std::ostream& out, Stats& stats) {
    std::string fatal;
    auto streamed = stream_proofs(in, [&](const ParsedProof& p) {
        if (!fatal.empty()) return;
        ++stats.blocks;
        stats.steps_in += p.steps.size();
        if (!p.unproved) {
            std::optional<Rewrite> r;
            try {
                r = rewrite(rt.context(), p);
            } catch (const std::exception&) {
            }
            if (r) {
                std::string text = Printer(&r->terms).block(r->proof);
                if (runs(rt, text)) {
                    out << text;
                    stats.steps_out += r->proof.steps.size();
                    return;
                }
            }
        }
        ++stats.as_given;
        stats.steps_out += p.steps.size();
        std::string text = Printer().block(p);
        out << text;
        if (runs(rt, text)) return;
        bool given = false;
        try {
            given = rt.execute_proof(p).ok();
        } catch (const std::exception&) {
        }
        if (given) {
            fatal = "'" + p.claim_name + "' checks as given but not as printed";
            return;
        }
        // Failing as given: unproved, as proof_checker registers it, so the blocks citing it still lower.
        auto claim = rt.context().find_claim(p.claim_name);
        if (!claim) claim = rt.context().find_known(p.claim_name);
        if (claim) rt.context().add_unproved_theorem(p.claim_name, claim.value());
    });
    if (!streamed.ok()) return streamed;
    if (!fatal.empty()) return MAKE_ERROR << fatal;
    return util::Ok();
}

}  // namespace logic::compress
