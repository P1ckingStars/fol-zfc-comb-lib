#include "src/machines/class/construction.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <functional>

namespace cls {
namespace {

// ------------------------------------------------------------------ the claim's name

std::string sha256_hex(const std::string& msg) {
    static const uint32_t K0[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
    uint32_t h[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    std::string m = msg;
    uint64_t bits = uint64_t(msg.size()) * 8;
    m.push_back(char(0x80));
    while (m.size() % 64 != 56) m.push_back(0);
    for (int i = 7; i >= 0; --i) m.push_back(char((bits >> (8 * i)) & 0xff));
    auto rot = [](uint32_t x, int n) { return (x >> n) | (x << (32 - n)); };
    for (size_t off = 0; off < m.size(); off += 64) {
        uint32_t w[64];
        for (int i = 0; i < 16; ++i)
            w[i] = (uint32_t(uint8_t(m[off + 4 * i])) << 24) | (uint32_t(uint8_t(m[off + 4 * i + 1])) << 16) |
                   (uint32_t(uint8_t(m[off + 4 * i + 2])) << 8) | uint32_t(uint8_t(m[off + 4 * i + 3]));
        for (int i = 16; i < 64; ++i) {
            uint32_t s0 = rot(w[i - 15], 7) ^ rot(w[i - 15], 18) ^ (w[i - 15] >> 3);
            uint32_t s1 = rot(w[i - 2], 17) ^ rot(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
        for (int i = 0; i < 64; ++i) {
            uint32_t t1 = hh + (rot(e, 6) ^ rot(e, 11) ^ rot(e, 25)) + ((e & f) ^ (~e & g)) + K0[i] + w[i];
            uint32_t t2 = (rot(a, 2) ^ rot(a, 13) ^ rot(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
            hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }
    char out[65];
    for (int i = 0; i < 8; ++i) std::snprintf(out + 8 * i, 9, "%08x", h[i]);
    return std::string(out, 64);
}

// ------------------------------------------------------------------ proof text

bool is_handle(const std::string& s) { return !s.empty() && s[0] == '_'; }

// A step that opens or closes no scope is written once while the scope it was written in is open: a later step of the
// same text is that step. A cited claim depends on no scope, so it is written once a proof.
class Proof {
public:
    int opened = 0;  // exists scopes left open until the end

    std::string line(const std::string& rhs, bool reuse = true) {
        if (reuse)
            if (auto it = seen_.find(rhs); it != seen_.end() && open(it->second.second)) return it->second.first;
        std::string h = "_h" + std::to_string(++n_);
        text_ += "    " + h + " = " + rhs + "\n";
        if (reuse) seen_[rhs] = {h, scopes_.back()};
        return h;
    }
    void raw(const std::string& s) { text_ += "    " + s + "\n"; }
    std::string text() const { return text_; }

    std::string use(const std::string& t) {
        auto it = used_.find(t);
        return it != used_.end() ? it->second : used_[t] = line("use " + t, false);
    }
    void fix(const std::string& v) {
        raw("fix " + v);
        push();
    }
    std::string assume(const std::string& f) {
        std::string h = line("assume " + f, false);
        push();
        return h;
    }
    std::string let(const std::string& f) { return line("let " + f, false); }
    // A variable instantiates a forall; a handle discharges an implication.
    std::string ch(std::string h, const std::vector<std::string>& xs) {
        for (const auto& x : xs) h = line((is_handle(x) ? "implies_elim " : "forall_elim ") + h + ", " + x);
        return h;
    }
    std::string ii(std::string h, int k = 1) {
        for (int i = 0; i < k; ++i) h = close("implies_intro " + h);
        return h;
    }
    std::string fi(const std::string& h) { return close("forall_intro " + h); }
    std::string ai(const std::string& a, const std::string& b) { return line("and_intro " + a + ", " + b); }
    std::string al(const std::string& h) { return line("and_elim_l " + h); }
    std::string ar(const std::string& h) { return line("and_elim_r " + h); }
    std::string iel(const std::string& h, const std::string& a) { return line("iff_elim_l " + h + ", " + a); }
    std::string ier(const std::string& h, const std::string& b) { return line("iff_elim_r " + h + ", " + b); }
    std::string iff(const std::string& f, const std::string& g) { return line("iff_intro " + f + ", " + g); }
    // An exists scope: `keep` scopes are closed by the caller, the others at the end.
    std::string ee(const std::string& h, const std::string& v, bool keep = false) {
        if (!keep) ++opened;
        std::string e = line("exists_elim " + h + ", " + v, false);
        push();
        return e;
    }
    std::string ei(const std::string& h) { return close("exists_intro " + h); }
    std::string ei(const std::string& h, const std::string& v) { return line("exists_intro " + h + ", " + v); }
    std::string oil(const std::string& h, const std::string& f) {
        std::string l = let(f);
        return line("or_intro_l " + h + ", " + l);
    }
    std::string oir(const std::string& f, const std::string& h) {
        std::string l = let(f);
        return line("or_intro_r " + l + ", " + h);
    }
    std::string oe(const std::string& d, const std::string& a, const std::string& b) {
        return line("or_elim " + d + ", " + a + ", " + b);
    }
    std::string ne(const std::string& n, const std::string& a) { return line("not_elim " + n + ", " + a); }
    std::string ni(const std::string& b) { return close("not_intro " + b); }
    std::string be(const std::string& b, const std::string& f) {
        std::string l = let(f);
        return line("bottom_elim " + b + ", " + l);
    }

private:
    int n_ = 0;
    std::string text_;
    std::map<std::string, std::string> used_;
    std::map<std::string, std::pair<std::string, int>> seen_;
    std::vector<int> scopes_ = {0};
    int next_ = 1;

    void push() { scopes_.push_back(next_++); }
    std::string close(const std::string& rhs) {
        scopes_.pop_back();
        return line(rhs, false);
    }
    bool open(int s) const { return std::find(scopes_.begin(), scopes_.end(), s) != scopes_.end(); }
};

std::string elem(const std::string& a, const std::string& b) { return "elem(" + a + ", " + b + ")"; }

// The text with each name in `m` replaced, whole names only.
std::string words(const std::string& text, const std::map<std::string, std::string>& m) {
    std::string out;
    for (size_t i = 0; i < text.size();) {
        if (std::isalpha(static_cast<unsigned char>(text[i])) || text[i] == '_') {
            size_t j = i;
            while (j < text.size() && (std::isalnum(static_cast<unsigned char>(text[j])) || text[j] == '_')) ++j;
            std::string w = text.substr(i, j - i);
            auto it = m.find(w);
            out += it == m.end() ? w : it->second;
            i = j;
        } else {
            out += text[i++];
        }
    }
    return out;
}

// ------------------------------------------------------------------ the construction

// A row: psi over its places, read by read1, read2 or read4; claim names a loaded one (DESIGN.md §10, decision 7).
struct RowEntry {
    Ptr psi;
    std::vector<std::string> places;
    std::string claim;
};

// A subformula over the variables in scope at it (FOUNDATION §3): the abstracted variable first, then each bound one.
// A rowed node is read through its row at the variables rargs.
struct Tree {
    Ptr f;
    std::vector<std::string> scope;
    std::vector<Tree> kids;
    bool rowed = false;
    const RowEntry* row = nullptr;
    std::vector<std::string> rargs;
};

std::set<std::string> free_vars(const Ptr& f) {
    std::set<std::string> out, bound;
    std::function<void(const Ptr&)> go = [&](const Ptr& g) {
        if (!g) return;
        if (g->k == K::Atom || g->k == K::Pred) {
            for (const auto& a : g->args)
                if (!bound.count(a)) out.insert(a);
            return;
        }
        if (g->k == K::All || g->k == K::Ex || g->k == K::Forall || g->k == K::Exists) {
            bool had = bound.count(g->name) > 0;
            bound.insert(g->name);
            go(g->a);
            if (!had) bound.erase(g->name);
            return;
        }
        go(g->a);
        go(g->b);
    };
    go(f);
    return out;
}

// f up to its bound variables' names, each free variable a hole: the key a row is looked up by.
std::string skeleton(const Ptr& f) {
    Fresh fb("_s");
    Ptr r = rename(f, {}, fb);
    std::map<std::string, std::string> m;
    for (const auto& v : free_vars(r)) m[v] = "_";
    return print(subst(r, m));
}

// g an instance of p: each of p's places one of g's free variables, the bound variables paired.
bool unify(const Ptr& p, const Ptr& g, const std::set<std::string>& places, std::map<std::string, std::string>& bind,
           std::map<std::string, std::string>& pair) {
    if (p->k != g->k) return false;
    switch (p->k) {
        case K::Atom:
        case K::Pred:
            if (p->name != g->name || p->args.size() != g->args.size()) return false;
            for (size_t i = 0; i < p->args.size(); ++i) {
                const std::string &pa = p->args[i], &ga = g->args[i];
                if (auto b = pair.find(pa); b != pair.end()) {
                    if (b->second != ga) return false;
                    continue;
                }
                for (const auto& [x, y] : pair)
                    if (y == ga) return false;
                if (!places.count(pa)) {
                    if (pa != ga) return false;
                    continue;
                }
                auto c = bind.find(pa);
                if (c == bind.end()) bind[pa] = ga;
                else if (c->second != ga) return false;
            }
            return true;
        case K::False: return true;
        case K::Not: return unify(p->a, g->a, places, bind, pair);
        case K::And:
        case K::Or:
        case K::Imp:
        case K::Iff: return unify(p->a, g->a, places, bind, pair) && unify(p->b, g->b, places, bind, pair);
        default: {
            auto old = pair.find(p->name);
            std::optional<std::string> saved;
            if (old != pair.end()) saved = old->second;
            pair[p->name] = g->name;
            bool ok = unify(p->a, g->a, places, bind, pair);
            if (saved) pair[p->name] = *saved;
            else pair.erase(p->name);
            return ok;
        }
    }
}

// A record's facts at N_0, N_1, ...: built from 0 by snoc, each of its exists scopes left for the caller to close.
struct Record {
    std::string r, sr, tr;
    std::vector<std::string> pm;
    size_t scopes = 0;
};

// The hypotheses at a record r of the scope's length k: set(r), tuple(r, N_k), and each entry y_i at N_i.
struct Rec {
    std::string r, sr, tr;
    std::vector<std::string> ys, sy, pm;  // pm[i] empty: entry i is read by no node here
    const std::string& pmem(size_t i) const {
        if (pm.at(i).empty()) throw std::logic_error("no fact for entry " + std::to_string(i) + " of a record");
        return pm[i];
    }
    std::vector<std::string> args() const {
        std::vector<std::string> out = {r, sr, tr};
        for (size_t i = 0; i < ys.size(); ++i) {
            out.push_back(ys[i]);
            out.push_back(sy[i]);
            out.push_back(pmem(i));
        }
        return out;
    }
};

class Machine {
public:
    Machine(const std::map<std::string, Def>& defs, const std::vector<Row>& rows,
            const std::vector<std::pair<std::string, bool>>& params)
        : defs_(defs) {
        for (const auto& [n, s] : params) {
            params_[n] = s;
            reserved_.insert(n);
        }
        for (const auto& r : rows) try {
                add_entry(guard(r.psi), r.places, r.claim);
            } catch (const Refused&) {
            }
    }

    Tree build(const Ptr& f, const std::vector<std::string>& scope) {
        auto in_scope = [&](const std::string& v) {
            for (const auto& s : scope)
                if (s == v) return true;
            return false;
        };
        if (auto r = row_for(f, scope)) {
            Tree t{f, scope, {}};
            t.rowed = true;
            t.row = r->first;
            t.rargs = r->second;
            return t;
        }
        switch (f->k) {
            case K::Atom: {
                for (size_t i = 0; i < f->args.size(); ++i) {
                    const auto& a = f->args[i];
                    if (in_scope(a)) continue;
                    if (!params_.count(a)) throw Refused("the variable " + a + " is free and no parameter");
                    if (!(f->name == "elem" && i == 1))
                        throw Refused("the parameter " + a + " outside a membership's right side in " + print(f));
                }
                return {f, scope, {}};
            }
            case K::False: return {f, scope, {}};
            case K::Pred: {
                auto it = defs_.find(f->name);
                if (it == defs_.end()) throw Refused("no @def for " + f->name);
                if (++depth_[f->name] > 64) throw Refused("the @def of " + f->name + " reaches itself");
                std::map<std::string, std::string> m;
                for (size_t i = 0; i < it->second.binders.size(); ++i) m[it->second.binders[i]] = f->args[i];
                Tree t{f, scope, {build(rename(guard(it->second.body), m, bound_), scope)}};
                --depth_[f->name];
                return t;
            }
            case K::Not: return {f, scope, {build(f->a, scope)}};
            case K::And:
            case K::Or:
            case K::Imp:
            case K::Iff: return {f, scope, {build(f->a, scope), build(f->b, scope)}};
            case K::All:
            case K::Ex: {
                auto inner = scope;
                inner.push_back(f->name);
                return {f, scope, {build(f->a, inner)}};
            }
            default: throw Refused("an unguarded quantifier");
        }
    }

    static size_t depth(const Tree& t) {
        size_t d = t.scope.size();
        for (const auto& k : t.kids) d = std::max(d, depth(k));
        return d;
    }

    Output run(const Request& req) {
        reserved_.insert(req.var);
        for (const auto& v : req.vars) reserved_.insert(v);
        if (req.shape == Shape::Row) return run_row(req);
        Ptr phi = rename(guard(req.formula), {}, bound_);
        plan(phi);
        plan_deep(phi, req.var);
        make_trees();
        Tree tree = build(phi, {req.var});
        size_t dmax = depth(tree);
        for (const auto& rt : rowtrees_) dmax = std::max(dmax, depth(rt.tree));
        auto phi_at = [&](const std::string& v) { return print(subst(phi, {{req.var, v}})); };

        std::map<std::string, std::string> bn;
        for (const char* b : {"z", "o", "c", "a", "w", "bd", "st"}) bn[b] = nm(b);
        auto T = [&](const std::string& text) { return words(text, bn); };
        const std::string w = bn.at("w");
        std::string body, tag;
        switch (req.shape) {
            case Shape::Exact:
                tag = "EXACT";
                body = T("(forall z. (set(z) -> (zero(z) -> (forall o. (set(o) -> (nsucc(z, o) -> (exists c. (forall a. "
                         "(set(a) -> (tuple(a, o) -> (forall w. (set(w) -> (pmem(z, w, a) -> (elem(a, c) <-> ") +
                       phi_at(w) + "))))))))))))))";
                break;
            case Shape::Val:
                tag = "VAL";
                body = T("(exists c. (forall w. (set(w) -> (elem(w, c) <-> ") + phi_at(w) + "))))";
                break;
            case Shape::Set:
                tag = "SET";
                body = T("(forall bd. (set(bd) -> (exists st. (set(st) & (forall w. (set(w) -> (elem(w, st) <-> "
                         "(elem(w, bd) & ") + phi_at(w) + "))))))))";
                break;
            case Shape::Class:
                tag = "CLASS";
                body = T("(exists c. (forall a. (set(a) -> (elem(a, c) <-> (exists w. (set(w) & ((forall z. (set(z) -> "
                         "(zero(z) -> snoc(z, z, w, a)))) & ") + phi_at(w) + ")))))))";
                break;
            case Shape::Row: break;
        }
        std::string stmt = body;
        for (auto it = req.params.rbegin(); it != req.params.rend(); ++it)
            stmt = it->second ? "(forall " + it->first + ". (set(" + it->first + ") -> " + stmt + "))"
                              : "(forall " + it->first + ". " + stmt + ")";
        Output out;
        out.name = "Cls." + tag + "_" + sha256_hex(stmt).substr(0, 16);
        out.statement = stmt;

        for (const auto& [n, s] : req.params) {
            p_.fix(n);
            if (s) p_.assume("set(" + n + ")");
        }
        N_ = {nm("N0")};
        std::string zz;
        if (req.shape == Shape::Exact) {
            N_.push_back(nm("N1"));
            p_.fix(N_[0]);
            sN_.push_back(p_.assume("set(" + N_[0] + ")"));
            zz = p_.assume("zero(" + N_[0] + ")");
            p_.fix(N_[1]);
            sN_.push_back(p_.assume("set(" + N_[1] + ")"));
            ns_.push_back(p_.assume("nsucc(" + N_[0] + ", " + N_[1] + ")"));
        } else {
            std::string e = p_.ee(p_.use("zero_EX"), N_[0]);
            sN_.push_back(p_.al(e));
            zz = p_.ar(e);
        }
        std::string nex = p_.use("nsucc_EX");
        while (N_.size() < dmax + 2) {
            size_t i = N_.size();
            std::string n = nm("N" + std::to_string(i));
            std::string e = p_.ee(p_.ch(nex, {N_[i - 1], sN_[i - 1]}), n);
            N_.push_back(n);
            sN_.push_back(p_.al(e));
            ns_.push_back(p_.ar(e));
        }
        zdef_ = p_.iel(p_.ch(p_.use("zero_def"), {N_[0]}), zz);
        snoc_facts_ = p_.use("snoc_facts");
        snoc_ex_ = p_.use("snoc_EX");
        make_rows();
        auto top = gen(tree);
        std::string Cphi = top.first, exphi = top.second;
        std::string N0 = N_[0], N1 = N_[1], sN0 = sN_[0], sN1 = sN_[1], ns0 = ns_[0];
        std::string tz = this->tz();

        std::string h;
        if (req.shape == Shape::Exact) {
            h = p_.ei(exphi, Cphi);
            for (int i = 0; i < p_.opened; ++i) h = p_.ei(h);
            h = p_.fi(p_.ii(h, 2));
            h = p_.fi(p_.ii(h, 2));
        } else if (req.shape == Shape::Class) {
            const std::string Tp = nm("Tp"), Ccls = nm("Ccls"), ev0 = nm("ev0"), ez0 = nm("ez0"), ex0 = nm("ex0");
            std::string tup = p_.ee(p_.ch(p_.use("tuples_class"), {N1, sN1}), Tp);
            std::string cc = p_.ee(p_.ch(p_.use("B2"), {Cphi, Tp}), Ccls);
            std::string a = nm("ea0");
            p_.fix(a);
            std::string sa = p_.assume("set(" + a + ")");
            std::string xb = p_.ch(cc, {a, sa}), tb = p_.ch(tup, {a, sa});
            std::string cp = p_.iel(xb, p_.assume(elem(a, Ccls)));
            std::string ta = p_.iel(tb, p_.ar(cp));
            std::string e = p_.ee(p_.ch(p_.use("tuple_first"), {N0, sN0, zz, N1, ns0, a, sa, ta}), ev0, true);
            std::string sv = p_.al(e), sn = p_.al(p_.ar(e)), pv = p_.ar(p_.ar(e));
            std::string ph = p_.iel(p_.ch(exphi, {a, sa, ta, ev0, sv, pv}), p_.al(cp));
            p_.fix(ez0);
            std::string sz = p_.assume("set(" + ez0 + ")"), zz0 = p_.assume("zero(" + ez0 + ")");
            std::string eqz = p_.ch(p_.use("zero_UNIQ"), {N0, sN0, ez0, sz, zz, zz0});
            std::string sc = p_.ch(p_.use("snoc_CONG"), {N0, ez0, N0, ez0, ev0, ev0, a, eqz, eqz,
                                                         p_.ch(p_.use("eq_refl"), {ev0}), sn});
            std::string t1 = p_.fi(p_.ii(sc, 2));
            std::string f1 = p_.ii(p_.ei(p_.ei(p_.ai(sv, p_.ai(t1, ph)), ev0)));
            std::string h2 = p_.assume(T("(exists w. (set(w) & ((forall z. (set(z) -> (zero(z) -> snoc(z, z, w, ") + a +
                                       ")))) & " + phi_at(w) + ")))");
            e = p_.ee(h2, ex0, true);
            std::string sx = p_.al(e), t1b = p_.al(p_.ar(e)), phb = p_.ar(p_.ar(e));
            std::string snb = p_.ch(t1b, {N0, sN0, zz});
            std::string sf = p_.ch(snoc_facts_, {N0, sN0, N1, sN1, ns0, N0, ex0, sx, a, tz, snb});
            std::string aC = p_.ier(p_.ch(exphi, {a, sa, p_.al(sf), ex0, sx, p_.al(p_.ar(sf))}), phb);
            std::string aT = p_.ier(tb, p_.al(sf));
            std::string g1 = p_.ii(p_.ei(p_.ier(xb, p_.ai(aC, aT))));
            h = p_.ei(p_.fi(p_.ii(p_.iff(f1, g1))), Ccls);
            for (int i = 0; i < p_.opened; ++i) h = p_.ei(h);
        } else {
            auto [Kc, kb] = val_class(phi, req.var, Cphi, exphi, nm("qv"), nm("et0"), nm("ea1"), nm("K"));
            if (req.shape == Shape::Val) {
                h = p_.ei(kb, Kc);
            } else {
                const std::string eb0 = nm("eb0"), es0 = nm("es0"), eu0 = nm("eu0");
                p_.fix(eb0);
                std::string sb = p_.assume("set(" + eb0 + ")");
                std::string e = p_.ee(p_.ch(p_.use("separation"), {Kc, eb0, sb}), es0, true);
                std::string ss = p_.al(e), sepb = p_.ar(e);
                p_.fix(eu0);
                std::string su = p_.assume("set(" + eu0 + ")");
                std::string xs = p_.ch(sepb, {eu0, su}), kk = p_.ch(kb, {eu0, su});
                std::string bk = p_.iel(xs, p_.assume(elem(eu0, es0)));
                std::string f1 = p_.ii(p_.ai(p_.al(bk), p_.iel(kk, p_.ar(bk))));
                std::string hb = p_.assume("(" + elem(eu0, eb0) + " & " + phi_at(eu0) + ")");
                std::string g1 = p_.ii(p_.ier(xs, p_.ai(p_.al(hb), p_.ier(kk, p_.ar(hb)))));
                std::string allu = p_.fi(p_.ii(p_.iff(f1, g1)));
                h = p_.ei(p_.ei(p_.ai(ss, allu), es0));
                h = p_.fi(p_.ii(h));
            }
            for (int i = 0; i < p_.opened; ++i) h = p_.ei(h);
        }
        for (auto it = req.params.rbegin(); it != req.params.rend(); ++it) h = p_.fi(it->second ? p_.ii(h) : h);
        p_.raw("qed " + h);
        out.proof = "proof " + out.name + ":\n" + p_.text();
        return out;
    }

private:
    // ---- rows (DESIGN.md §10, decisions 3 to 7) ----

    // A row made here: psi's tuples as pairs, phi(z), and psi's node in phi's tree, whose class carries equals.
    struct RowTree {
        const RowEntry* e = nullptr;
        size_t n = 0;
        std::string z;
        std::vector<std::string> enc;
        Ptr phi;
        Tree tree;
        const Tree* pnode = nullptr;
    };

    std::deque<RowEntry> entries_;
    std::multimap<std::string, const RowEntry*> by_skel_;
    std::set<std::string> pred_rowed_, seen_;
    std::set<const RowEntry*> building_;
    std::set<const Node*> skip_;
    std::vector<const RowEntry*> order_;
    std::deque<RowTree> rowtrees_;
    std::map<const RowEntry*, std::pair<std::string, std::string>> local_, loaded_;
    std::map<const Tree*, std::pair<std::string, std::string>> made_;
    std::string tz_;

    const RowEntry* add_entry(Ptr psi, std::vector<std::string> places, std::string claim) {
        entries_.push_back(RowEntry{std::move(psi), std::move(places), std::move(claim)});
        const RowEntry* e = &entries_.back();
        by_skel_.emplace(skeleton(e->psi), e);
        if (e->psi->k == K::Pred && e->psi->args == e->places) pred_rowed_.insert(e->psi->name);
        return e;
    }

    // The row f is read through at this scope: one whose formula f is an instance of, each place a variable in scope.
    using RowAt = std::pair<const RowEntry*, std::vector<std::string>>;
    std::optional<RowAt> row_for(const Ptr& f, const std::vector<std::string>& scope) const {
        if (f->k == K::Atom || f->k == K::False || skip_.count(f.get())) return {};
        auto range = by_skel_.equal_range(skeleton(f));
        for (auto it = range.first; it != range.second; ++it) {
            const RowEntry* e = it->second;
            if (building_.count(e) || e->places.empty() || e->places.size() > 4) continue;
            if (building_trees_ && e->claim.empty() && !available_.count(e)) continue;
            std::set<std::string> places(e->places.begin(), e->places.end());
            std::map<std::string, std::string> bind, pair;
            if (!unify(e->psi, f, places, bind, pair)) continue;
            std::vector<std::string> args;
            for (const auto& pl : e->places) {
                auto b = bind.find(pl);
                if (b == bind.end() || std::find(scope.begin(), scope.end(), b->second) == scope.end()) break;
                args.push_back(b->second);
            }
            if (args.size() == e->places.size()) return std::make_pair(e, args);
        }
        return {};
    }

    // The rows to make here, after those their definitions read: each defined predicate of 1 to 4 places with none.
    void plan(const Ptr& f) {
        if (!f) return;
        if (f->k == K::Pred) {
            const std::string& P = f->name;
            auto d = defs_.find(P);
            if (d == defs_.end() || pred_rowed_.count(P) || seen_.count(P)) return;
            seen_.insert(P);
            plan(d->second.body);
            size_t n = f->args.size();
            if (n >= 1 && n <= 4) {
                std::vector<std::string> places;
                for (size_t i = 0; i < n; ++i) places.push_back(bound_());
                order_.push_back(add_entry(atom(P, places), places, ""));
            }
            return;
        }
        plan(f->a);
        plan(f->b);
    }

    void row_tree(const RowEntry* e) {
        size_t n = e->places.size();
        RowTree rt;
        rt.e = e;
        rt.n = n;
        rt.z = bound_();
        std::string q, x, p;
        if (n == 1) {
            rt.enc = {rt.z};
        } else if (n == 2) {
            rt.enc = {bound_(), bound_()};
        } else {
            q = bound_();
            x = bound_();
            p = bound_();
            rt.enc = {bound_(), bound_(), bound_()};
            if (n == 4) rt.enc.push_back(x);
        }
        std::map<std::string, std::string> m;
        for (size_t i = 0; i < n; ++i) m[e->places[i]] = rt.enc[i];
        Ptr psi = rename(e->psi, m, bound_);
        skip_.insert(psi.get());
        if (n == 1) {
            rt.phi = psi;
        } else if (n == 2) {
            const std::string &u = rt.enc[0], &v = rt.enc[1];
            rt.phi = quant(K::Ex, u, quant(K::Ex, v, binary(K::And, atom("kpair", {u, v, rt.z}), psi)));
        } else {
            const std::string &u = rt.enc[0], &v = rt.enc[1], &w = rt.enc[2];
            Ptr in = quant(K::Ex, v, quant(K::Ex, w, binary(K::And, atom("kpair", {v, w, p}), psi)));
            Ptr mid = quant(K::Ex, p, quant(K::Ex, u, binary(K::And, atom("kpair", {p, u, q}), in)));
            rt.phi = quant(K::Ex, q, quant(K::Ex, x, binary(K::And, atom("kpair", {q, x, rt.z}), mid)));
        }
        building_.insert(e);
        rt.tree = build(rt.phi, {rt.z});
        building_.erase(e);
        rowtrees_.push_back(std::move(rt));
        RowTree& back = rowtrees_.back();
        std::function<void(const Tree&)> find = [&](const Tree& t) {
            if (!back.pnode && t.f.get() == psi.get()) back.pnode = &t;
            for (const auto& c : t.kids) find(c);
        };
        find(back.tree);
        if (!back.pnode) throw Refused("no node of a row's formula in its tree");
        forced_.insert(back.pnode);
    }

    std::string tz() {
        if (tz_.empty()) tz_ = p_.ch(p_.use("tuple_zero"), {N_[0], zdef_});
        return tz_;
    }

    // ---- rows made in the request for its subformulas (DESIGN.md §10, decision 8) ----

    bool building_trees_ = false;
    std::set<const RowEntry*> available_;

    void make_trees() {
        building_trees_ = true;
        for (const RowEntry* e : order_) {
            row_tree(e);
            available_.insert(e);
        }
        building_trees_ = false;
    }

    // The lines the machine writes, fitted to its output: a quantifier pays for each entry its body reads, a row for
    // its encoding and each read of it.
    static constexpr double kQuant = 35, kVar = 3, kNode = 10, kAtom = 22, kRead = 22;
    static double row_cost(size_t n) { return n == 1 ? 40 : n == 2 ? 360 : 780; }
    static size_t row_depth(size_t n) { return n == 1 ? 1 : n == 2 ? 3 : 7; }

    std::map<const Node*, std::pair<Ptr, Ptr>> unfolded_;
    Ptr unfold(const Ptr& f) {
        auto it = unfolded_.find(f.get());
        if (it != unfolded_.end()) return it->second.second;
        const Def& d = defs_.at(f->name);
        std::map<std::string, std::string> m;
        for (size_t i = 0; i < d.binders.size(); ++i) m[d.binders[i]] = f->args[i];
        Ptr u = rename(guard(d.body), m, bound_);
        unfolded_[f.get()] = {f, u};
        return u;
    }

    double est(const Ptr& f, std::vector<std::string>& scope, int depth = 0) {
        if (row_for(f, scope)) return kRead;
        switch (f->k) {
            case K::All:
            case K::Ex: {
                std::set<std::string> fv = free_vars(f->a);
                double c = kQuant;
                for (const auto& v : scope) c += kVar * fv.count(v);
                scope.push_back(f->name);
                c += est(f->a, scope, depth);
                scope.pop_back();
                return c;
            }
            case K::Not: return kNode + est(f->a, scope, depth);
            case K::And:
            case K::Or:
            case K::Imp:
            case K::Iff: return kNode + est(f->a, scope, depth) + est(f->b, scope, depth);
            case K::Pred:
                if (!defs_.count(f->name) || depth > 64) return kAtom;
                return kNode + est(unfold(f), scope, depth + 1);
            default: return kAtom;
        }
    }

    size_t usize(const Ptr& f, int depth = 0) {
        if (!f) return 0;
        if (f->k == K::Pred)
            return 1 + (defs_.count(f->name) && !pred_rowed_.count(f->name) && depth <= 64 ? usize(unfold(f), depth + 1)
                                                                                          : 0);
        return 1 + usize(f->a, depth) + usize(f->b, depth);
    }

    static void first_seen(const Ptr& f, const std::set<std::string>& in, std::vector<std::string>& out) {
        if (!f) return;
        if (f->k == K::Atom || f->k == K::Pred) {
            for (const auto& a : f->args)
                if (in.count(a) && std::find(out.begin(), out.end(), a) == out.end()) out.push_back(a);
            return;
        }
        first_seen(f->a, in, out);
        first_seen(f->b, in, out);
    }

    struct Occ {
        Ptr f;
        std::vector<std::string> scope;
    };

    // Each subformula a row could be read at: one to four places in scope, its other free variables parameters; keyed
    // by its text with the places named by first appearance, so one key is one row.
    void occurrences(const Ptr& f, std::vector<std::string>& scope, std::map<std::string, std::vector<Occ>>& out,
                     int depth = 0) {
        if (!f || f->k == K::Atom || f->k == K::False || f->k == K::Forall || f->k == K::Exists || row_for(f, scope))
            return;
        std::set<std::string> in(scope.begin(), scope.end());
        std::vector<std::string> places;
        first_seen(f, in, places);
        bool ok = !places.empty() && places.size() <= 4;
        for (const auto& v : free_vars(f))
            if (!in.count(v) && !params_.count(v)) ok = false;
        if (ok) {
            std::map<std::string, std::string> m;
            for (size_t i = 0; i < places.size(); ++i) m[places[i]] = "_p" + std::to_string(i);
            Fresh fr("_b");
            out[print(rename(f, m, fr))].push_back({f, scope});
        }
        switch (f->k) {
            case K::All:
            case K::Ex:
                scope.push_back(f->name);
                occurrences(f->a, scope, out, depth);
                scope.pop_back();
                return;
            case K::Pred:
                if (defs_.count(f->name) && depth <= 64) occurrences(unfold(f), scope, out, depth + 1);
                return;
            default:
                occurrences(f->a, scope, out, depth);
                occurrences(f->b, scope, out, depth);
        }
    }

    // A row for each subformula, deep or repeated, whose occurrences cost more than the row and its reads, the one that
    // saves most first; each proved after the rows its formula reads.
    void plan_deep(const Ptr& phi, const std::string& var) {
        struct Made {
            const RowEntry* e;
            std::vector<std::string> inner;
            size_t size;
        };
        std::vector<Made> made;
        for (int round = 0; round < 256; ++round) {
            std::map<std::string, std::vector<Occ>> groups;
            std::vector<std::string> scope = {var};
            occurrences(phi, scope, groups);
            for (auto& m : made) {
                const Ptr& psi = m.e->psi;
                std::vector<std::string> in = m.inner;
                if (psi->k == K::All || psi->k == K::Ex) {
                    in.push_back(psi->name);
                    occurrences(psi->a, in, groups);
                } else if (psi->k == K::Pred) {
                    if (defs_.count(psi->name)) occurrences(unfold(psi), in, groups, 1);
                } else {
                    occurrences(psi->a, in, groups);
                    occurrences(psi->b, in, groups);
                }
            }
            double best = 0;
            Ptr bpsi;
            std::vector<std::string> bown, binner;
            for (const auto& [key, occs] : groups) {
                double here = 0;
                for (const auto& o : occs) {
                    auto sc = o.scope;
                    here += est(o.f, sc);
                }
                std::set<std::string> in(occs[0].scope.begin(), occs[0].scope.end());
                std::vector<std::string> places, own;
                first_seen(occs[0].f, in, places);
                if (here - kRead * occs.size() - row_cost(places.size()) <= best) continue;
                std::map<std::string, std::string> m;
                for (const auto& v : places) m[v] = own.emplace_back(bound_());
                Ptr psi = rename(occs[0].f, m, bound_);
                std::vector<std::string> inner = own;
                while (inner.size() < row_depth(own.size())) inner.insert(inner.begin(), bound_());
                auto sc = inner;
                double g = here - kRead * occs.size() - row_cost(own.size()) - est(psi, sc);
                if (g > best) {
                    best = g;
                    bpsi = psi;
                    bown = own;
                    binner = inner;
                }
            }
            if (!bpsi) break;
            made.push_back({add_entry(bpsi, bown, ""), binner, usize(bpsi)});
        }
        std::stable_sort(made.begin(), made.end(), [](const Made& a, const Made& b) { return a.size < b.size; });
        for (const auto& m : made) order_.push_back(m.e);
    }

    void make_rows() {
        if (rowtrees_.empty()) return;
        tz();
        for (const auto& rt : rowtrees_) local_[rt.e] = prove_row(rt);
    }

    // A row's class and iff: a loaded one opened once, or the one made here.
    std::pair<std::string, std::string> row_of(const RowEntry* e) {
        if (auto l = local_.find(e); l != local_.end()) return l->second;
        if (auto l = loaded_.find(e); l != loaded_.end()) return l->second;
        std::string w = rowk_();
        std::string h = p_.ee(p_.use(e->claim), w);
        return loaded_[e] = {w, h};
    }

    std::string at_places(const RowEntry* e, const std::vector<std::string>& args) {
        std::map<std::string, std::string> m;
        for (size_t i = 0; i < args.size(); ++i) m[e->places[i]] = args[i];
        return print(rename(e->psi, m, bound_));
    }

    // phi's class at the 1-records made a class of sets by member_class: K with forall w. (w in K <-> phi(w)).
    std::pair<std::string, std::string> val_class(const Ptr& phi, const std::string& var, const std::string& Cphi,
                                                  const std::string& exphi, const std::string& qv,
                                                  const std::string& et0, const std::string& ea1,
                                                  const std::string& Kc) {
        auto at = [&](const std::string& v) { return print(subst(phi, {{var, v}})); };
        std::string mc = p_.line("schema_inst member_class { Q: \\" + qv + ". " + at(qv) + " }");
        p_.fix(et0);
        std::string st = p_.assume("set(" + et0 + ")");
        p_.fix(ea1);
        std::string sa1 = p_.assume("set(" + ea1 + ")");
        std::string sn = p_.assume("snoc(" + N_[0] + ", " + N_[0] + ", " + et0 + ", " + ea1 + ")");
        std::string sf = p_.ch(snoc_facts_, {N_[0], sN_[0], N_[1], sN_[1], ns_[0], N_[0], et0, st, ea1, tz(), sn});
        std::string ex1 = p_.ch(exphi, {ea1, sa1, p_.al(sf), et0, st, p_.al(p_.ar(sf))});
        std::string prem = p_.fi(p_.ii(p_.fi(p_.ii(p_.ii(ex1)))));
        return {Kc, p_.ee(p_.ch(mc, {N_[0], sN_[0], Cphi, N_[0], sN_[0], prem}), Kc)};
    }

    Record make_record(const std::vector<std::string>& ys, const std::vector<std::string>& sy) {
        Record R;
        R.r = N_[0];
        R.sr = sN_[0];
        R.tr = tz();
        for (size_t i = 0; i < ys.size(); ++i) {
            std::string b = eigen_();
            std::string e = p_.ee(p_.ch(snoc_ex_, {R.r, R.sr, N_[i], sN_[i], ys[i], sy[i]}), b, true);
            ++R.scopes;
            std::string sb = p_.al(e), sn = p_.ar(e);
            std::string sf =
                p_.ch(snoc_facts_, {N_[i], sN_[i], N_[i + 1], sN_[i + 1], ns_[i], R.r, ys[i], sy[i], b, R.tr, sn});
            std::string keep = p_.ar(p_.ar(sf));
            for (size_t j = 0; j < i; ++j) R.pm[j] = p_.ch(keep, {N_[j], ys[j], R.pm[j]});
            R.pm.push_back(p_.al(p_.ar(sf)));
            R.r = b;
            R.sr = sb;
            R.tr = p_.al(sf);
        }
        return R;
    }

    // P at `to` from P at `from`, eq(from_i, to_i) each: both read in the class of P's node, at one record.
    std::string carry(const RowTree& rt, const std::vector<std::string>& from, const std::vector<std::string>& sfrom,
                      const std::vector<std::string>& to, const std::vector<std::string>& sto,
                      const std::vector<std::string>& eqs, const std::string& at_from) {
        const Tree& pn = *rt.pnode;
        const std::string exp = made_.at(&pn).second;
        size_t m = pn.scope.size();
        std::vector<size_t> pos;
        for (const auto& a : rt.enc)
            for (size_t i = 0; i < m; ++i)
                if (pn.scope[i] == a) {
                    pos.push_back(i);
                    break;
                }
        std::vector<std::string> ys(m, N_[0]), sy(m, sN_[0]);
        for (size_t i = 0; i < pos.size(); ++i) {
            ys[pos[i]] = to[i];
            sy[pos[i]] = sto[i];
        }
        Record rec = make_record(ys, sy);
        std::vector<std::string> ys2 = ys, sy2 = sy, pm2 = rec.pm;
        for (size_t i = 0; i < pos.size(); ++i) {
            ys2[pos[i]] = from[i];
            sy2[pos[i]] = sfrom[i];
            pm2[pos[i]] = p_.ch(p_.use("g2_pmem_cong"), {N_[pos[i]], from[i], to[i], rec.r, eqs[i], rec.pm[pos[i]]});
        }
        using Strs = std::vector<std::string>;
        auto args = [&](const Strs& y, const Strs& s, const Strs& pm) {
            std::vector<std::string> out = {rec.r, rec.sr, rec.tr};
            for (size_t i = 0; i < m; ++i) out.insert(out.end(), {y[i], s[i], pm[i]});
            return out;
        };
        std::string in = p_.ier(p_.ch(exp, args(ys2, sy2, pm2)), at_from);
        std::string h = p_.iel(p_.ch(exp, args(ys, sy, rec.pm)), in);
        for (size_t i = 0; i < rec.scopes; ++i) h = p_.ei(h);
        return h;
    }

    // P's row, proved here: phi's class a class of sets by member_class, then the iff the reading rows take.
    std::pair<std::string, std::string> prove_row(const RowTree& rt) {
        auto [Cphi, exphi] = gen(rt.tree);
        auto [K, kb] = val_class(rt.phi, rt.z, Cphi, exphi, nm("qv"), eigen_(), eigen_(), rowk_());
        if (rt.n == 1) return {K, kb};
        if (rt.n == 2) {
            std::string u = eigen_(), v = eigen_();
            p_.fix(u);
            std::string su = p_.assume("set(" + u + ")");
            p_.fix(v);
            std::string sv = p_.assume("set(" + v + ")");
            std::string h = p_.assume("pmem(" + u + ", " + v + ", " + K + ")");
            std::string p = eigen_();
            std::string e = p_.ee(p_.iel(p_.ch(p_.use("pmem_def"), {u, v, K}), h), p, true);
            std::string sp = p_.al(e), kp = p_.al(p_.ar(e)), pK = p_.ar(p_.ar(e));
            std::string ph = p_.iel(p_.ch(kb, {p, sp}), pK);
            std::string u2 = eigen_();
            std::string e1 = p_.ee(ph, u2, true);
            std::string su2 = p_.al(e1);
            std::string v2 = eigen_();
            std::string e2 = p_.ee(p_.ar(e1), v2, true);
            std::string sv2 = p_.al(e2), kp2 = p_.al(p_.ar(e2)), P2 = p_.ar(p_.ar(e2));
            std::string inj = p_.ch(p_.use("pair_inj"), {u2, v2, u, v, p, kp2, kp});
            std::string puv = carry(rt, {u2, v2}, {su2, sv2}, {u, v}, {su, sv}, {p_.al(inj), p_.ar(inj)}, P2);
            std::string f1 = p_.ii(p_.ei(p_.ei(p_.ei(puv))));
            std::string hp = p_.assume(at_places(rt.e, {u, v}));
            std::string p3 = eigen_();
            std::string e3 = p_.ee(p_.ch(p_.use("pair_ex"), {u, v, su, sv}), p3, true);
            std::string sp3 = p_.al(e3), kp3 = p_.ar(e3);
            std::string phw = p_.ei(p_.ai(su, p_.ei(p_.ai(sv, p_.ai(kp3, hp)), v)), u);
            std::string pk3 = p_.ier(p_.ch(kb, {p3, sp3}), phw);
            std::string pm = p_.ier(p_.ch(p_.use("pmem_def"), {u, v, K}), p_.ei(p_.ai(sp3, p_.ai(kp3, pk3)), p3));
            std::string g1 = p_.ii(p_.ei(pm));
            return {K, p_.fi(p_.ii(p_.fi(p_.ii(p_.iff(f1, g1)))))};
        }
        std::vector<std::string> xs = {eigen_(), eigen_(), eigen_(), eigen_()}, sx;
        for (const auto& y : xs) {
            p_.fix(y);
            sx.push_back(p_.assume("set(" + y + ")"));
        }
        const std::string &u = xs[0], &v = xs[1], &w = xs[2], &x = xs[3];
        std::vector<std::string> pargs = {u, v, w};
        if (rt.n == 4) pargs.push_back(x);
        const std::string bp = bound_(), bq = bound_();
        std::string L = "(exists " + bp + ". (set(" + bp + ") & (kpair(" + v + ", " + w + ", " + bp + ") & (exists " +
                        bq + ". (set(" + bq + ") & (kpair(" + bp + ", " + u + ", " + bq + ") & pmem(" + bq + ", " + x +
                        ", " + K + ")))))))";
        std::string hl = p_.assume(L);
        std::string p = eigen_(), q = eigen_(), z = eigen_();
        std::string ep = p_.ee(hl, p, true);
        std::string kvw = p_.al(p_.ar(ep));
        std::string eq_ = p_.ee(p_.ar(p_.ar(ep)), q, true);
        std::string kpu = p_.al(p_.ar(eq_)), pq = p_.ar(p_.ar(eq_));
        std::string ez = p_.ee(p_.iel(p_.ch(p_.use("pmem_def"), {q, x, K}), pq), z, true);
        std::string sz = p_.al(ez), kqx = p_.al(p_.ar(ez)), zK = p_.ar(p_.ar(ez));
        std::string cur = p_.iel(p_.ch(kb, {z, sz}), zK);
        std::vector<std::string> ws, sws, ks;
        for (int lvl = 0; lvl < 3; ++lvl) {
            for (int j = 0; j < 2; ++j) {
                std::string y = eigen_();
                std::string e = p_.ee(cur, y, true);
                ws.push_back(y);
                sws.push_back(p_.al(e));
                cur = p_.ar(e);
            }
            ks.push_back(p_.al(cur));
            cur = p_.ar(cur);
        }
        const std::string &q2 = ws[0], &x2 = ws[1], &p2 = ws[2], &u2 = ws[3], &v2 = ws[4], &w2 = ws[5];
        std::string i1 = p_.ch(p_.use("pair_inj"), {q2, x2, q, x, z, ks[0], kqx});
        std::string kq = p_.ch(p_.use("kpair_res_cong"), {p2, u2, q2, q, ks[1], p_.al(i1)});
        std::string i2 = p_.ch(p_.use("pair_inj"), {p2, u2, p, u, q, kq, kpu});
        std::string kv = p_.ch(p_.use("kpair_res_cong"), {v2, w2, p2, p, ks[2], p_.al(i2)});
        std::string i3 = p_.ch(p_.use("pair_inj"), {v2, w2, v, w, p, kv, kvw});
        std::vector<std::string> from = {u2, v2, w2}, sfrom = {sws[3], sws[4], sws[5]};
        std::vector<std::string> to = {u, v, w}, sto = {sx[0], sx[1], sx[2]};
        std::vector<std::string> eqs = {p_.ar(i2), p_.al(i3), p_.ar(i3)};
        if (rt.n == 4) {
            from.push_back(x2);
            sfrom.push_back(sws[1]);
            to.push_back(x);
            sto.push_back(sx[3]);
            eqs.push_back(p_.ar(i1));
        }
        std::string pt = carry(rt, from, sfrom, to, sto, eqs, cur);
        for (int i = 0; i < 9; ++i) pt = p_.ei(pt);
        std::string f1 = p_.ii(pt);
        std::string hp = p_.assume(at_places(rt.e, pargs));
        std::string p3 = eigen_(), q3 = eigen_(), z3 = eigen_();
        std::string a1 = p_.ee(p_.ch(p_.use("pair_ex"), {v, w, sx[1], sx[2]}), p3, true);
        std::string sp3 = p_.al(a1), kvw3 = p_.ar(a1);
        std::string a2 = p_.ee(p_.ch(p_.use("pair_ex"), {p3, u, sp3, sx[0]}), q3, true);
        std::string sq3 = p_.al(a2), kpu3 = p_.ar(a2);
        std::string a3 = p_.ee(p_.ch(p_.use("pair_ex"), {q3, x, sq3, sx[3]}), z3, true);
        std::string sz3 = p_.al(a3), kqx3 = p_.ar(a3);
        std::string in3 = p_.ei(p_.ai(sx[1], p_.ei(p_.ai(sx[2], p_.ai(kvw3, hp)), w)), v);
        std::string in2 = p_.ei(p_.ai(sp3, p_.ei(p_.ai(sx[0], p_.ai(kpu3, in3)), u)), p3);
        std::string in1 = p_.ei(p_.ai(sq3, p_.ei(p_.ai(sx[3], p_.ai(kqx3, in2)), x)), q3);
        std::string zK3 = p_.ier(p_.ch(kb, {z3, sz3}), in1);
        std::string pq3 = p_.ier(p_.ch(p_.use("pmem_def"), {q3, x, K}), p_.ei(p_.ai(sz3, p_.ai(kqx3, zK3)), z3));
        std::string l3 = p_.ei(p_.ai(sp3, p_.ai(kvw3, p_.ei(p_.ai(sq3, p_.ai(kpu3, pq3)), q3))), p3);
        std::string g1 = p_.ii(p_.ei(p_.ei(p_.ei(l3))));
        std::string h4 = p_.iff(f1, g1);
        for (int i = 0; i < 4; ++i) h4 = p_.fi(p_.ii(h4));
        return {K, h4};
    }

    // A ROW request: its formula's row, the rows its predicates need made first, in the same proof.
    Output run_row(const Request& req) {
        size_t n = req.vars.size();
        if (!req.params.empty() || n < 1 || n > 4)
            throw Refused("a ROW request has one to four places and no parameters");
        Ptr psi = rename(guard(req.formula), {}, bound_);
        std::set<std::string> fv = free_vars(psi);
        for (const auto& v : req.vars)
            if (!fv.count(v)) throw Refused("the place " + v + " is not in the formula");
        if (fv.size() != n) throw Refused("a free variable of the formula is no place");
        const RowEntry* e = add_entry(psi, req.vars, "");
        building_.insert(e);
        if (psi->k == K::Pred && defs_.count(psi->name)) {
            seen_.insert(psi->name);
            plan(defs_.at(psi->name).body);
        } else {
            plan(psi);
        }
        make_trees();
        building_.erase(e);
        row_tree(e);
        size_t dmax = 1;
        for (const auto& rt : rowtrees_) dmax = std::max(dmax, depth(rt.tree));
        N_ = {nm("N0")};
        std::string e0 = p_.ee(p_.use("zero_EX"), N_[0]);
        sN_.push_back(p_.al(e0));
        std::string zz = p_.ar(e0);
        std::string nex = p_.use("nsucc_EX");
        while (N_.size() < dmax + 2) {
            size_t i = N_.size();
            std::string nn = nm("N" + std::to_string(i));
            std::string ex = p_.ee(p_.ch(nex, {N_[i - 1], sN_[i - 1]}), nn);
            N_.push_back(nn);
            sN_.push_back(p_.al(ex));
            ns_.push_back(p_.ar(ex));
        }
        zdef_ = p_.iel(p_.ch(p_.use("zero_def"), {N_[0]}), zz);
        snoc_facts_ = p_.use("snoc_facts");
        snoc_ex_ = p_.use("snoc_EX");
        make_rows();
        auto [K, wb] = local_.at(e);
        Output out;
        out.statement = row_statement(psi, req.vars);
        out.name = "Cls.ROW_" + sha256_hex(out.statement).substr(0, 16);
        std::string h = p_.ei(wb, K);
        for (int i = 0; i < p_.opened; ++i) h = p_.ei(h);
        p_.raw("qed " + h);
        out.proof = "proof " + out.name + ":\n" + p_.text();
        return out;
    }

    const std::map<std::string, Def>& defs_;
    std::map<std::string, bool> params_;
    std::map<std::string, int> depth_;
    std::set<std::string> reserved_;
    Fresh bound_{"v", &reserved_}, eigen_{"e", &reserved_}, cls_{"C", &reserved_}, rowk_{"W", &reserved_};

    // A name the construction writes: `want`, unless the request uses it, as no name it writes may be the request's.
    std::string nm(const std::string& want) const {
        std::string s = want;
        for (int k = 1; reserved_.count(s); ++k) s = want + "_" + std::to_string(k);
        return s;
    }
    Proof p_;
    std::vector<std::string> N_, sN_, ns_;
    std::string zdef_, snoc_facts_, snoc_ex_;
    std::map<size_t, std::string> sf_;  // snoc_facts at N_k and N_k+1
    std::map<std::string, std::pair<std::string, std::string>> glob_;
    std::string rsk_;

    // A witness class from base, opened once.
    std::pair<std::string, std::string> witness(const std::string& key) {
        auto it = glob_.find(key);
        if (it != glob_.end()) return it->second;
        static const std::map<std::string, std::string> lemma = {
            {"E", "B1"}, {"D", "cls_diag"}, {"Z", "cls_zero"}, {"Ns", "cls_nsucc"}, {"S", "cls_snoc4"}};
        std::string w = nm("W" + key);
        std::string e = p_.ee(p_.use(lemma.at(key)), w);
        glob_[key] = {w, e};
        if (key == "S") rsk_ = p_.ch(p_.use("rs_key"), {w, e});
        return glob_[key];
    }

    // EX at the node: for every record r of length k with entries y, elem(r, C) <-> psi(y); its proof from core.
    std::string ex_lemma(size_t k, const std::function<std::string(const Rec&)>& core) {
        Rec R;
        R.r = eigen_();
        p_.fix(R.r);
        R.sr = p_.assume("set(" + R.r + ")");
        R.tr = p_.assume("tuple(" + R.r + ", " + N_[k] + ")");
        for (size_t i = 0; i < k; ++i) {
            std::string y = eigen_();
            p_.fix(y);
            R.ys.push_back(y);
            R.sy.push_back(p_.assume("set(" + y + ")"));
            R.pm.push_back(p_.assume("pmem(" + N_[i] + ", " + y + ", " + R.r + ")"));
        }
        std::string h = core(R);
        for (size_t i = k; i-- > 0;) h = p_.fi(p_.ii(h, 2));
        return p_.fi(p_.ii(h, 2));
    }

    std::string text_at(const Tree& t, const std::vector<std::string>& ys) {
        std::map<std::string, std::string> m;
        for (size_t i = 0; i < t.scope.size(); ++i) m[t.scope[i]] = ys[i];
        return print(subst(t.f, m));
    }

    // What a read row says of entries ys of a class W: read1's, read2's or read4's right side.
    std::string read_form(const std::vector<std::string>& ys, const std::string& W) {
        if (ys.size() == 1) return elem(ys[0], W);
        if (ys.size() == 2) return "pmem(" + ys[0] + ", " + ys[1] + ", " + W + ")";
        std::string p = bound_(), q = bound_();
        return "(exists " + p + ". (set(" + p + ") & (kpair(" + ys[1] + ", " + ys[2] + ", " + p + ") & (exists " + q +
               ". (set(" + q + ") & (kpair(" + p + ", " + ys[0] + ", " + q + ") & pmem(" + q + ", " + ys[3] + ", " + W +
               ")))))))";
    }

    // x <-> z from h1, x <-> y, and h2, y <-> z, by base's schema iff_trans.
    std::string trans(const std::string& h1, const std::string& h2, const std::string& x, const std::string& y,
                      const std::string& z) {
        return p_.ch(p_.line("schema_inst iff_trans { A: " + x + ", B: " + y + ", C: " + z + " }"), {h1, h2});
    }

    // ---- the construction in two passes (DESIGN.md §10, decisions 6, 8 and 9) ----

    // A node's class, made first, at the proof's top, and what its iff reads besides.
    struct NodeCls {
        std::string C, cb, wb, pdef, op, W;
        std::vector<size_t> ix;
    };
    std::map<const Tree*, NodeCls> nc_;
    std::set<const Tree*> forced_;

    std::pair<std::string, std::string> gen(const Tree& t) {
        classes(t);
        return {nc_.at(&t).C, segment(t)};
    }

    // The first pass: every node's class, its children's first.
    void classes(const Tree& t) {
        for (const auto& c : t.kids) classes(c);
        const Ptr& f = t.f;
        size_t k = t.scope.size();
        std::map<std::string, size_t> idx;
        for (size_t i = 0; i < k; ++i) idx[t.scope[i]] = i;
        const auto& N = N_;
        const auto& sN = sN_;
        NodeCls n;
        if (t.rowed) {
            const auto rw = row_of(t.row);
            n.wb = rw.second;
            n.W = rw.first;
            for (const auto& a : t.rargs) n.ix.push_back(idx.at(a));
            size_t np = n.ix.size();
            if (np == 3) n.ix.push_back(n.ix[2]);
            std::vector<std::string> rargs;
            for (size_t i : n.ix) rargs.insert(rargs.end(), {N[i], sN[i]});
            rargs.push_back(rw.first);
            n.C = cls_();
            n.cb = p_.ee(p_.ch(p_.use(np == 1 ? "read1" : np == 2 ? "read2" : "read4"), rargs), n.C);
        } else if (f->k == K::Atom) {
            n.op = f->name;
            if (n.op == "set") {
                n.ix = {idx.at(f->args[0])};
                n.C = cls_();
                n.cb = p_.ee(p_.ch(p_.use("B3"), {N[0]}), n.C);
            } else if (n.op == "elem" && params_.count(f->args[1])) {
                n.op = "elem of a parameter";
                n.ix = {idx.at(f->args[0])};
                n.C = cls_();
                n.cb = p_.ee(p_.ch(p_.use("read1"), {N[n.ix[0]], sN[n.ix[0]], f->args[1]}), n.C);
            } else if (n.op == "elem" || n.op == "eq" || n.op == "nsucc") {
                auto wit = witness(n.op == "elem" ? "E" : n.op == "eq" ? "D" : "Ns");
                n.wb = wit.second;
                n.W = wit.first;
                n.ix = {idx.at(f->args[0]), idx.at(f->args[1])};
                n.C = cls_();
                n.cb = p_.ee(p_.ch(p_.use("read2"), {N[n.ix[0]], sN[n.ix[0]], N[n.ix[1]], sN[n.ix[1]], wit.first}),
                             n.C);
            } else if (n.op == "zero") {
                auto wit = witness("Z");
                n.wb = wit.second;
                n.W = wit.first;
                n.ix = {idx.at(f->args[0])};
                n.C = cls_();
                n.cb = p_.ee(p_.ch(p_.use("read1"), {N[n.ix[0]], sN[n.ix[0]], wit.first}), n.C);
            } else if (n.op == "snoc") {
                std::string W = witness("S").first;
                n.W = W;
                for (const auto& a : f->args) n.ix.push_back(idx.at(a));
                n.C = cls_();
                n.cb = p_.ee(p_.ch(p_.use("read4"), {N[n.ix[0]], sN[n.ix[0]], N[n.ix[1]], sN[n.ix[1]], N[n.ix[2]],
                                                     sN[n.ix[2]], N[n.ix[3]], sN[n.ix[3]], W}),
                             n.C);
            } else {
                throw Refused("the atom " + print(f));
            }
        } else if (f->k == K::False) {
            n.C = N[0];
        } else if (f->k == K::Pred) {
            n.C = nc_.at(&t.kids[0]).C;
            n.pdef = p_.use(defs_.at(f->name).axiom);
        } else if (f->k == K::Not) {
            n.C = cls_();
            n.cb = p_.ee(p_.ch(p_.use("B3"), {nc_.at(&t.kids[0]).C}), n.C);
        } else if (f->k == K::And || f->k == K::Or || f->k == K::Imp || f->k == K::Iff) {
            std::string row = f->k == K::And ? "B2" : f->k == K::Or ? "B_or" : f->k == K::Imp ? "B_imp" : "B_iff";
            n.C = cls_();
            n.cb = p_.ee(p_.ch(p_.use(row), {nc_.at(&t.kids[0]).C, nc_.at(&t.kids[1]).C}), n.C);
        } else {
            n.C = cls_();
            n.cb = p_.ee(p_.ch(p_.use(f->k == K::Ex ? "row_ex" : "row_all"), {N[k], sN[k], nc_.at(&t.kids[0]).C}), n.C);
            if (!sf_.count(k)) sf_[k] = p_.ch(snoc_facts_, {N[k], sN[k], N[k + 1], sN[k + 1], ns_[k]});
        }
        nc_[&t] = n;
    }

    // A stretch between quantifiers proved in one scope: its root's iff for every record of the root's length. The
    // lemmas it cites, its quantifiers' bodies and its forced nodes, are proved before it, each at the proof's top.
    std::string segment(const Tree& t) {
        prepare(t, true);
        std::string ex = ex_lemma(t.scope.size(), [&](const Rec& R) { return iff(t, R, true); });
        made_[&t] = {nc_.at(&t).C, ex};
        return ex;
    }

    void prepare(const Tree& t, bool root) {
        if (t.rowed) return;
        if (!root && forced_.count(&t)) {
            if (!made_.count(&t)) segment(t);
            return;
        }
        for (const auto& c : t.kids) prepare(c, false);
    }

    std::map<const Tree*, bool> has_forced_;
    bool has_forced(const Tree& t) {
        auto it = has_forced_.find(&t);
        if (it != has_forced_.end()) return it->second;
        bool h = forced_.count(&t) > 0;
        for (const auto& c : t.kids) h = has_forced(c) || h;
        return has_forced_[&t] = h;
    }

    // The second pass: elem(R.r, C) <-> the node's formula at R's entries, in R's scope.
    std::string iff(const Tree& t, const Rec& R, bool root = false) {
        if (!root && forced_.count(&t)) return p_.ch(made_.at(&t).second, R.args());
        const Ptr& f = t.f;
        size_t k = t.scope.size();
        const NodeCls& n = nc_.at(&t);
        const auto& N = N_;
        const std::string& C = n.C;
        if (t.rowed || (f->k == K::Atom && n.op == "snoc")) {
            std::vector<std::string> args = {R.r, R.sr, N[k], R.tr}, bargs, ys;
            for (size_t i : n.ix) {
                args.insert(args.end(), {R.ys[i], R.sy[i], R.pmem(i)});
                bargs.insert(bargs.end(), {R.ys[i], R.sy[i]});
                ys.push_back(R.ys[i]);
            }
            return trans(p_.ch(n.cb, args), p_.ch(t.rowed ? n.wb : rsk_, bargs), elem(R.r, C), read_form(ys, n.W),
                         text_at(t, R.ys));
        }
        if (f->k == K::Atom) {
            size_t i = n.ix[0];
            if (n.op == "set") {
                std::string rb = p_.ch(n.cb, {R.r, R.sr});
                p_.assume(elem(R.r, C));
                std::string f1 = p_.ii(R.sy[i]);
                p_.assume("set(" + R.ys[i] + ")");
                std::string g1 = p_.ii(p_.ier(rb, p_.ch(zdef_, {R.r, R.sr})));
                return p_.iff(f1, g1);
            }
            if (n.op == "elem of a parameter") return p_.ch(n.cb, {R.r, R.sr, N[k], R.tr, R.ys[i], R.sy[i], R.pmem(i)});
            if (n.op == "zero") {
                std::string r1 = p_.ch(n.cb, {R.r, R.sr, N[k], R.tr, R.ys[i], R.sy[i], R.pmem(i)});
                return trans(r1, p_.ch(n.wb, {R.ys[i], R.sy[i]}), elem(R.r, C), elem(R.ys[i], n.W),
                             "zero(" + R.ys[i] + ")");
            }
            size_t j = n.ix[1];
            std::string r2 =
                p_.ch(n.cb, {R.r, R.sr, N[k], R.tr, R.ys[i], R.sy[i], R.pmem(i), R.ys[j], R.sy[j], R.pmem(j)});
            std::string b = n.op == "elem" ? p_.ch(n.wb, {R.ys[i], R.ys[j], R.sy[i], R.sy[j]})
                                           : p_.ch(n.wb, {R.ys[i], R.sy[i], R.ys[j], R.sy[j]});
            return trans(r2, b, elem(R.r, C), read_form({R.ys[i], R.ys[j]}, n.W),
                         n.op + "(" + R.ys[i] + ", " + R.ys[j] + ")");
        }
        if (f->k == K::False) {
            std::string hr = p_.assume(elem(R.r, C));
            std::string f1 = p_.ii(p_.ne(p_.ch(zdef_, {R.r, R.sr}), hr));
            std::string g1 = p_.ii(p_.be(p_.assume("false"), elem(R.r, C)));
            return p_.iff(f1, g1);
        }
        if (f->k == K::Pred) {
            std::map<std::string, std::string> m;
            for (size_t i = 0; i < t.scope.size(); ++i) m[t.scope[i]] = R.ys[i];
            std::vector<std::string> args;
            for (const auto& a : f->args) args.push_back(m.count(a) ? m[a] : a);
            std::string inst = p_.ch(n.pdef, args);
            std::string e1 = iff(t.kids[0], R);
            std::string f1 = p_.ii(p_.ier(inst, p_.iel(e1, p_.assume(elem(R.r, C)))));
            std::string g1 = p_.ii(p_.ier(e1, p_.iel(inst, p_.assume(print(atom(f->name, args))))));
            return p_.iff(f1, g1);
        }
        // A connective: its row's iff at r and its children's, by the machine's schema for it (rows/steps).
        if (f->k == K::Not) {
            std::string rb = p_.ch(n.cb, {R.r, R.sr});
            std::string ea = iff(t.kids[0], R);
            return p_.ch(p_.line("schema_inst node_not { X: " + elem(R.r, C) + ", P: " +
                                 elem(R.r, nc_.at(&t.kids[0]).C) + ", A: " + text_at(t.kids[0], R.ys) + " }"),
                         {rb, ea});
        }
        if (f->k == K::And || f->k == K::Or || f->k == K::Imp || f->k == K::Iff) {
            std::string rb = p_.ch(n.cb, {R.r, R.sr});
            std::string ea = iff(t.kids[0], R), eb = iff(t.kids[1], R);
            const char* sch = f->k == K::And   ? "node_and"
                              : f->k == K::Or  ? "node_or"
                              : f->k == K::Imp ? "node_imp"
                                               : "node_iff";
            return p_.ch(p_.line(std::string("schema_inst ") + sch + " { X: " + elem(R.r, C) + ", P: " +
                                 elem(R.r, nc_.at(&t.kids[0]).C) + ", Q: " + elem(R.r, nc_.at(&t.kids[1]).C) +
                                 ", A: " + text_at(t.kids[0], R.ys) + ", B: " + text_at(t.kids[1], R.ys) + " }"),
                         {rb, ea, eb});
        }
        // All and Ex: the bound variable has index k, its record the snoc of r at N_k. The body is proved in place at
        // every such snoc once, for both directions, with the facts of the entries it reads.
        bool ex = f->k == K::Ex;
        const Tree& bt = t.kids[0];
        std::string at_every;
        {
            std::string v = eigen_();
            p_.fix(v);
            std::string sv = p_.assume("set(" + v + ")");
            std::string b = eigen_();
            p_.fix(b);
            std::string sb = p_.assume("set(" + b + ")");
            std::string sn = p_.assume("snoc(" + R.r + ", " + N[k] + ", " + v + ", " + b + ")");
            std::string sf = p_.ch(sf_.at(k), {R.r, v, sv, b, R.tr, sn});
            Rec B;
            B.r = b;
            B.sr = sb;
            B.tr = p_.al(sf);
            std::string pv = p_.al(p_.ar(sf)), keep = p_.ar(p_.ar(sf));
            bool all = has_forced(bt);
            std::set<std::string> used = free_vars(bt.f);
            for (size_t i = 0; i < k; ++i) {
                B.ys.push_back(R.ys[i]);
                B.sy.push_back(R.sy[i]);
                B.pm.push_back(all || used.count(t.scope[i]) ? p_.ch(keep, {N[i], R.ys[i], R.pmem(i)}) : "");
            }
            B.ys.push_back(v);
            B.sy.push_back(sv);
            B.pm.push_back(pv);
            at_every = p_.fi(p_.ii(p_.fi(p_.ii(p_.ii(iff(bt, B))))));
        }
        std::vector<std::string> ys = R.ys;
        std::string w = bound_();
        ys.push_back(w);
        std::string inst = p_.line(std::string("schema_inst ") + (ex ? "node_ex" : "node_all") + " { P: \\" + w + ". " +
                                   text_at(bt, ys) + " }");
        return p_.ch(inst, {R.r, R.sr, N[k], sN_[k], nc_.at(&bt).C, C, n.cb, at_every});
    }
};

}  // namespace

Output construct(const Request& req, const std::map<std::string, Def>& defs, const std::vector<Row>& rows) {
    Machine m(defs, rows, req.params);
    return m.run(req);
}

namespace {

Ptr some_of(const std::string& v, Ptr body) {
    return quant(K::Exists, v, binary(K::And, atom("set", {v}), std::move(body)));
}

}  // namespace

std::string row_statement(const Ptr& psi, const std::vector<std::string>& places) {
    std::set<std::string> taken(places.begin(), places.end());
    std::function<void(const Ptr&)> names = [&](const Ptr& g) {
        if (!g) return;
        if (g->k == K::Atom || g->k == K::Pred) taken.insert(g->args.begin(), g->args.end());
        else if (!g->name.empty()) taken.insert(g->name);
        names(g->a);
        names(g->b);
    };
    names(psi);
    auto fresh = [&](const std::string& want) {
        std::string s = want;
        for (int k = 1; taken.count(s); ++k) s = want + std::to_string(k);
        taken.insert(s);
        return s;
    };
    const std::string W = fresh("W");
    std::vector<std::string> vs = places;
    if (vs.size() == 3) vs.push_back(fresh("x"));
    std::string L;
    if (vs.size() == 1) {
        L = elem(vs[0], W);
    } else if (vs.size() == 2) {
        L = "pmem(" + vs[0] + ", " + vs[1] + ", " + W + ")";
    } else {
        const std::string p = fresh("p"), q = fresh("q");
        L = "(exists " + p + ". (set(" + p + ") & (kpair(" + vs[1] + ", " + vs[2] + ", " + p + ") & (exists " + q +
            ". (set(" + q + ") & (kpair(" + p + ", " + vs[0] + ", " + q + ") & pmem(" + q + ", " + vs[3] + ", " + W +
            ")))))))";
    }
    std::string body = "(" + L + " <-> " + print(psi) + ")";
    for (size_t i = vs.size(); i-- > 0;) body = "(forall " + vs[i] + ". (set(" + vs[i] + ") -> " + body + "))";
    return "(exists " + W + ". " + body + ")";
}

std::optional<Row> as_row(const Ptr& f) {
    if (f->k != K::Exists) return {};
    const std::string W = f->name;
    Ptr g = f->a;
    std::vector<std::string> vs;
    while (g->k == K::Forall && g->a && g->a->k == K::Imp && g->a->a->k == K::Atom && g->a->a->name == "set" &&
           g->a->a->args == std::vector<std::string>{g->name}) {
        vs.push_back(g->name);
        g = g->a->b;
    }
    if (g->k != K::Iff || vs.empty() || vs.size() == 3 || vs.size() > 4) return {};
    const Ptr &L = g->a, &psi = g->b;
    std::set<std::string> fv = free_vars(psi);
    std::vector<std::string> places = vs;
    if (vs.size() == 4 && !fv.count(vs[3])) places.pop_back();
    for (const auto& v : fv)
        if (std::find(places.begin(), places.end(), v) == places.end()) return {};
    for (const auto& v : places)
        if (!fv.count(v)) return {};
    Ptr want;
    if (vs.size() == 1) want = atom("elem", {vs[0], W});
    else if (vs.size() == 2) want = atom("pmem", {vs[0], vs[1], W});
    else
        want = some_of("_p", binary(K::And, atom("kpair", {vs[1], vs[2], "_p"}),
                                    some_of("_q", binary(K::And, atom("kpair", {"_p", vs[0], "_q"}),
                                                         atom("pmem", {"_q", vs[3], W})))));
    Fresh f1("c"), f2("c");
    if (print(rename(L, {}, f1)) != print(rename(want, {}, f2))) return {};
    return Row{"", psi, places};
}

}  // namespace cls
