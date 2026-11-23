#include "src/machines/class/construction.h"

#include <array>
#include <cstdint>
#include <cstdio>
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

class Proof {
public:
    int opened = 0;  // exists scopes left open until the end

    std::string line(const std::string& rhs) {
        std::string h = "_h" + std::to_string(++n_);
        text_ += "    " + h + " = " + rhs + "\n";
        return h;
    }
    void raw(const std::string& s) { text_ += "    " + s + "\n"; }
    std::string text() const { return text_; }

    std::string use(const std::string& t) { return line("use " + t); }
    void fix(const std::string& v) { raw("fix " + v); }
    std::string assume(const std::string& f) { return line("assume " + f); }
    std::string let(const std::string& f) { return line("let " + f); }
    // A variable instantiates a forall; a handle discharges an implication.
    std::string ch(std::string h, const std::vector<std::string>& xs) {
        for (const auto& x : xs) h = line((is_handle(x) ? "implies_elim " : "forall_elim ") + h + ", " + x);
        return h;
    }
    std::string ii(std::string h, int k = 1) {
        for (int i = 0; i < k; ++i) h = line("implies_intro " + h);
        return h;
    }
    std::string fi(const std::string& h) { return line("forall_intro " + h); }
    std::string ai(const std::string& a, const std::string& b) { return line("and_intro " + a + ", " + b); }
    std::string al(const std::string& h) { return line("and_elim_l " + h); }
    std::string ar(const std::string& h) { return line("and_elim_r " + h); }
    std::string iel(const std::string& h, const std::string& a) { return line("iff_elim_l " + h + ", " + a); }
    std::string ier(const std::string& h, const std::string& b) { return line("iff_elim_r " + h + ", " + b); }
    std::string iff(const std::string& f, const std::string& g) { return line("iff_intro " + f + ", " + g); }
    // An exists scope: `keep` scopes are closed by the caller, the others at the end.
    std::string ee(const std::string& h, const std::string& v, bool keep = false) {
        if (!keep) ++opened;
        return line("exists_elim " + h + ", " + v);
    }
    std::string ei(const std::string& h) { return line("exists_intro " + h); }
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
    std::string ni(const std::string& b) { return line("not_intro " + b); }
    std::string be(const std::string& b, const std::string& f) {
        std::string l = let(f);
        return line("bottom_elim " + b + ", " + l);
    }

private:
    int n_ = 0;
    std::string text_;
};

std::string elem(const std::string& a, const std::string& b) { return "elem(" + a + ", " + b + ")"; }

// ------------------------------------------------------------------ the construction

// A subformula over the variables in scope at it (FOUNDATION §3): the abstracted variable first, then each bound one.
struct Tree {
    Ptr f;
    std::vector<std::string> scope;
    std::vector<Tree> kids;
};

// The hypotheses at a record r of the scope's length k: set(r), tuple(r, N_k), and each entry y_i at N_i.
struct Rec {
    std::string r, sr, tr;
    std::vector<std::string> ys, sy, pm;
    std::vector<std::string> args() const {
        std::vector<std::string> out = {r, sr, tr};
        for (size_t i = 0; i < ys.size(); ++i) {
            out.push_back(ys[i]);
            out.push_back(sy[i]);
            out.push_back(pm[i]);
        }
        return out;
    }
};

class Machine {
public:
    Machine(const std::map<std::string, Def>& defs, const std::vector<std::pair<std::string, bool>>& params)
        : defs_(defs) {
        for (const auto& [n, s] : params) params_[n] = s;
    }

    Tree build(const Ptr& f, const std::vector<std::string>& scope) {
        auto in_scope = [&](const std::string& v) {
            for (const auto& s : scope)
                if (s == v) return true;
            return false;
        };
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
        Ptr phi = rename(guard(req.formula), {}, bound_);
        Tree tree = build(phi, {req.var});
        size_t dmax = depth(tree);
        auto phi_at = [&](const std::string& v) { return print(subst(phi, {{req.var, v}})); };

        std::string body, tag;
        switch (req.shape) {
            case Shape::Exact:
                tag = "EXACT";
                body = "(forall z. (set(z) -> (zero(z) -> (forall o. (set(o) -> (nsucc(z, o) -> (exists c. (forall a. "
                       "(set(a) -> (tuple(a, o) -> (forall w. (set(w) -> (pmem(z, w, a) -> (elem(a, c) <-> " +
                       phi_at("w") + "))))))))))))))";
                break;
            case Shape::Val:
                tag = "VAL";
                body = "(exists c. (forall w. (set(w) -> (elem(w, c) <-> " + phi_at("w") + "))))";
                break;
            case Shape::Set:
                tag = "SET";
                body = "(forall bd. (set(bd) -> (exists st. (set(st) & (forall w. (set(w) -> (elem(w, st) <-> "
                       "(elem(w, bd) & " + phi_at("w") + "))))))))";
                break;
            case Shape::Class:
                tag = "CLASS";
                body = "(exists c. (forall a. (set(a) -> (elem(a, c) <-> (exists w. (set(w) & ((forall z. (set(z) -> "
                       "(zero(z) -> snoc(z, z, w, a)))) & " + phi_at("w") + ")))))))";
                break;
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
        N_ = {"N0"};
        std::string zz;
        if (req.shape == Shape::Exact) {
            p_.fix("N0");
            sN_.push_back(p_.assume("set(N0)"));
            zz = p_.assume("zero(N0)");
            p_.fix("N1");
            sN_.push_back(p_.assume("set(N1)"));
            ns_.push_back(p_.assume("nsucc(N0, N1)"));
            N_.push_back("N1");
        } else {
            std::string e = p_.ee(p_.use("zero_EX"), "N0");
            sN_.push_back(p_.al(e));
            zz = p_.ar(e);
        }
        std::string nex = p_.use("nsucc_EX");
        while (N_.size() < dmax + 2) {
            size_t i = N_.size();
            std::string n = "N" + std::to_string(i);
            std::string e = p_.ee(p_.ch(nex, {N_[i - 1], sN_[i - 1]}), n);
            N_.push_back(n);
            sN_.push_back(p_.al(e));
            ns_.push_back(p_.ar(e));
        }
        zdef_ = p_.iel(p_.ch(p_.use("zero_def"), {"N0"}), zz);
        snoc_facts_ = p_.use("snoc_facts");
        snoc_ex_ = p_.use("snoc_EX");
        auto top = gen(tree);
        std::string Cphi = top.first, exphi = top.second;
        std::string N0 = "N0", N1 = "N1", sN0 = sN_[0], sN1 = sN_[1], ns0 = ns_[0];
        std::string tz = p_.ch(p_.use("tuple_zero"), {N0, zdef_});

        std::string h;
        if (req.shape == Shape::Exact) {
            h = p_.ei(exphi, Cphi);
            for (int i = 0; i < p_.opened; ++i) h = p_.ei(h);
            h = p_.fi(p_.ii(h, 2));
            h = p_.fi(p_.ii(h, 2));
        } else if (req.shape == Shape::Class) {
            std::string tup = p_.ee(p_.ch(p_.use("tuples_class"), {N1, sN1}), "Tp");
            std::string cc = p_.ee(p_.ch(p_.use("B2"), {Cphi, "Tp"}), "Ccls");
            std::string a = "ea0";
            p_.fix(a);
            std::string sa = p_.assume("set(" + a + ")");
            std::string xb = p_.ch(cc, {a, sa}), tb = p_.ch(tup, {a, sa});
            std::string cp = p_.iel(xb, p_.assume(elem(a, "Ccls")));
            std::string ta = p_.iel(tb, p_.ar(cp));
            std::string e = p_.ee(p_.ch(p_.use("tuple_first"), {N0, sN0, zz, N1, ns0, a, sa, ta}), "ev0", true);
            std::string sv = p_.al(e), sn = p_.al(p_.ar(e)), pv = p_.ar(p_.ar(e));
            std::string ph = p_.iel(p_.ch(exphi, {a, sa, ta, "ev0", sv, pv}), p_.al(cp));
            p_.fix("ez0");
            std::string sz = p_.assume("set(ez0)"), zz0 = p_.assume("zero(ez0)");
            std::string eqz = p_.ch(p_.use("zero_UNIQ"), {N0, sN0, "ez0", sz, zz, zz0});
            std::string sc = p_.ch(p_.use("snoc_CONG"), {N0, "ez0", N0, "ez0", "ev0", "ev0", a, eqz, eqz,
                                                         p_.ch(p_.use("eq_refl"), {"ev0"}), sn});
            std::string t1 = p_.fi(p_.ii(sc, 2));
            std::string f1 = p_.ii(p_.ei(p_.ei(p_.ai(sv, p_.ai(t1, ph)), "ev0")));
            std::string h2 = p_.assume("(exists w. (set(w) & ((forall z. (set(z) -> (zero(z) -> snoc(z, z, w, " + a +
                                       ")))) & " + phi_at("w") + ")))");
            e = p_.ee(h2, "ex0", true);
            std::string sx = p_.al(e), t1b = p_.al(p_.ar(e)), phb = p_.ar(p_.ar(e));
            std::string snb = p_.ch(t1b, {N0, sN0, zz});
            std::string sf = p_.ch(snoc_facts_, {N0, sN0, N1, sN1, ns0, N0, "ex0", sx, a, tz, snb});
            std::string aC = p_.ier(p_.ch(exphi, {a, sa, p_.al(sf), "ex0", sx, p_.al(p_.ar(sf))}), phb);
            std::string aT = p_.ier(tb, p_.al(sf));
            std::string g1 = p_.ii(p_.ei(p_.ier(xb, p_.ai(aC, aT))));
            h = p_.ei(p_.fi(p_.ii(p_.iff(f1, g1))), "Ccls");
            for (int i = 0; i < p_.opened; ++i) h = p_.ei(h);
        } else {
            std::string mc = p_.line("schema_inst member_class { Q: \\qv. " + phi_at("qv") + " }");
            p_.fix("et0");
            std::string st = p_.assume("set(et0)");
            p_.fix("ea1");
            std::string sa1 = p_.assume("set(ea1)");
            std::string sn = p_.assume("snoc(" + N0 + ", " + N0 + ", et0, ea1)");
            std::string sf = p_.ch(snoc_facts_, {N0, sN0, N1, sN1, ns0, N0, "et0", st, "ea1", tz, sn});
            std::string ex1 = p_.ch(exphi, {"ea1", sa1, p_.al(sf), "et0", st, p_.al(p_.ar(sf))});
            std::string prem = p_.fi(p_.ii(p_.fi(p_.ii(p_.ii(ex1)))));
            std::string kb = p_.ee(p_.ch(mc, {N0, sN0, Cphi, N0, sN0, prem}), "K");
            if (req.shape == Shape::Val) {
                h = p_.ei(kb, "K");
            } else {
                p_.fix("eb0");
                std::string sb = p_.assume("set(eb0)");
                std::string e = p_.ee(p_.ch(p_.use("separation"), {"K", "eb0", sb}), "es0", true);
                std::string ss = p_.al(e), sepb = p_.ar(e);
                p_.fix("eu0");
                std::string su = p_.assume("set(eu0)");
                std::string xs = p_.ch(sepb, {"eu0", su}), kk = p_.ch(kb, {"eu0", su});
                std::string bk = p_.iel(xs, p_.assume(elem("eu0", "es0")));
                std::string f1 = p_.ii(p_.ai(p_.al(bk), p_.iel(kk, p_.ar(bk))));
                std::string hb = p_.assume("(" + elem("eu0", "eb0") + " & " + phi_at("eu0") + ")");
                std::string g1 = p_.ii(p_.ier(xs, p_.ai(p_.al(hb), p_.ier(kk, p_.ar(hb)))));
                std::string allu = p_.fi(p_.ii(p_.iff(f1, g1)));
                h = p_.ei(p_.ei(p_.ai(ss, allu), "es0"));
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
    const std::map<std::string, Def>& defs_;
    std::map<std::string, bool> params_;
    std::map<std::string, int> depth_;
    Fresh bound_{"v"}, eigen_{"e"}, cls_{"C"};
    Proof p_;
    std::vector<std::string> N_, sN_, ns_;
    std::string zdef_, snoc_facts_, snoc_ex_;
    std::map<std::string, std::pair<std::string, std::string>> glob_;
    std::string rsk_;

    // A witness class from base, opened once.
    std::pair<std::string, std::string> witness(const std::string& key) {
        auto it = glob_.find(key);
        if (it != glob_.end()) return it->second;
        static const std::map<std::string, std::string> lemma = {
            {"E", "B1"}, {"D", "cls_diag"}, {"Z", "cls_zero"}, {"Ns", "cls_nsucc"}, {"S", "cls_snoc4"}};
        std::string w = "W" + key;
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

    std::string iff_trans(const std::string& h1, const std::string& h2, const std::string& x, const std::string& z) {
        std::string f = p_.ii(p_.iel(h2, p_.iel(h1, p_.assume(x))));
        std::string g = p_.ii(p_.ier(h1, p_.ier(h2, p_.assume(z))));
        return p_.iff(f, g);
    }

    // From X <-> (P op Q), P <-> A and Q <-> B: X <-> (A op B).
    std::string cong(K op, const std::string& rb, const std::string& ea, const std::string& eb, const std::string& X,
                     const std::string& P, const std::string& Q, const std::string& A, const std::string& B) {
        std::string pq = p_.iel(rb, p_.assume(X));
        if (op == K::And) {
            std::string f = p_.ii(p_.ai(p_.iel(ea, p_.al(pq)), p_.iel(eb, p_.ar(pq))));
            std::string hab = p_.assume("(" + A + " & " + B + ")");
            std::string g = p_.ii(p_.ier(rb, p_.ai(p_.ier(ea, p_.al(hab)), p_.ier(eb, p_.ar(hab)))));
            return p_.iff(f, g);
        }
        if (op == K::Or) {
            std::string c1 = p_.ii(p_.oil(p_.iel(ea, p_.assume(P)), B));
            std::string c2 = p_.ii(p_.oir(A, p_.iel(eb, p_.assume(Q))));
            std::string f = p_.ii(p_.oe(pq, c1, c2));
            std::string hab = p_.assume("(" + A + " | " + B + ")");
            std::string d1 = p_.ii(p_.ier(rb, p_.oil(p_.ier(ea, p_.assume(A)), Q)));
            std::string d2 = p_.ii(p_.ier(rb, p_.oir(P, p_.ier(eb, p_.assume(B)))));
            std::string g = p_.ii(p_.oe(hab, d1, d2));
            return p_.iff(f, g);
        }
        if (op == K::Imp) {
            std::string ha = p_.assume(A);
            std::string f = p_.ii(p_.ii(p_.iel(eb, p_.ch(pq, {p_.ier(ea, ha)}))));
            std::string hab = p_.assume("(" + A + " -> " + B + ")");
            std::string hp = p_.assume(P);
            std::string g = p_.ii(p_.ier(rb, p_.ii(p_.ier(eb, p_.ch(hab, {p_.iel(ea, hp)})))));
            return p_.iff(f, g);
        }
        std::string ab = p_.ii(p_.iel(eb, p_.iel(pq, p_.ier(ea, p_.assume(A)))));
        std::string ba = p_.ii(p_.iel(ea, p_.ier(pq, p_.ier(eb, p_.assume(B)))));
        std::string f = p_.ii(p_.iff(ab, ba));
        std::string hab = p_.assume("(" + A + " <-> " + B + ")");
        std::string pq1 = p_.ii(p_.ier(eb, p_.iel(hab, p_.iel(ea, p_.assume(P)))));
        std::string qp = p_.ii(p_.ier(ea, p_.ier(hab, p_.iel(eb, p_.assume(Q)))));
        std::string g = p_.ii(p_.ier(rb, p_.iff(pq1, qp)));
        return p_.iff(f, g);
    }

    std::string cong_not(const std::string& rb, const std::string& ea, const std::string& X, const std::string& P,
                         const std::string& A) {
        std::string np = p_.iel(rb, p_.assume(X));
        std::string ha = p_.assume(A);
        std::string f = p_.ii(p_.ni(p_.ne(np, p_.ier(ea, ha))));
        std::string hna = p_.assume("(~ " + A + ")");
        std::string hp = p_.assume(P);
        std::string g = p_.ii(p_.ier(rb, p_.ni(p_.ne(hna, p_.iel(ea, hp)))));
        return p_.iff(f, g);
    }

    // The class of a node and its EX lemma.
    std::pair<std::string, std::string> gen(const Tree& t) {
        const Ptr& f = t.f;
        size_t k = t.scope.size();
        std::map<std::string, size_t> idx;
        for (size_t i = 0; i < k; ++i) idx[t.scope[i]] = i;
        const auto& N = N_;
        const auto& sN = sN_;

        if (f->k == K::Atom) {
            const std::string& op = f->name;
            if (op == "set") {
                size_t i = idx.at(f->args[0]);
                std::string C = cls_();
                std::string compl_ = p_.ee(p_.ch(p_.use("B3"), {N[0]}), C);
                return {C, ex_lemma(k, [&, i, C, compl_](const Rec& R) {
                            std::string rb = p_.ch(compl_, {R.r, R.sr});
                            p_.assume(elem(R.r, C));
                            std::string f1 = p_.ii(R.sy[i]);
                            p_.assume("set(" + R.ys[i] + ")");
                            std::string g1 = p_.ii(p_.ier(rb, p_.ch(zdef_, {R.r, R.sr})));
                            return p_.iff(f1, g1);
                        })};
            }
            if (op == "elem" && params_.count(f->args[1])) {
                size_t i = idx.at(f->args[0]);
                std::string C = cls_();
                std::string cb = p_.ee(p_.ch(p_.use("read1"), {N[i], sN[i], f->args[1]}), C);
                return {C, ex_lemma(k, [&, i, cb](const Rec& R) {
                            return p_.ch(cb, {R.r, R.sr, N[k], R.tr, R.ys[i], R.sy[i], R.pm[i]});
                        })};
            }
            if (op == "elem" || op == "eq" || op == "nsucc") {
                auto wit = witness(op == "elem" ? "E" : op == "eq" ? "D" : "Ns");
                std::string W = wit.first, wb = wit.second;
                size_t i = idx.at(f->args[0]), j = idx.at(f->args[1]);
                std::string C = cls_();
                std::string cb = p_.ee(p_.ch(p_.use("read2"), {N[i], sN[i], N[j], sN[j], W}), C);
                return {C, ex_lemma(k, [&, i, j, C, cb, wb, op](const Rec& R) {
                            std::string r2 = p_.ch(cb, {R.r, R.sr, N[k], R.tr, R.ys[i], R.sy[i], R.pm[i], R.ys[j],
                                                        R.sy[j], R.pm[j]});
                            std::string b = op == "elem" ? p_.ch(wb, {R.ys[i], R.ys[j], R.sy[i], R.sy[j]})
                                                         : p_.ch(wb, {R.ys[i], R.sy[i], R.ys[j], R.sy[j]});
                            return iff_trans(r2, b, elem(R.r, C), op + "(" + R.ys[i] + ", " + R.ys[j] + ")");
                        })};
            }
            if (op == "zero") {
                auto wit = witness("Z");
                std::string W = wit.first, wb = wit.second;
                size_t i = idx.at(f->args[0]);
                std::string C = cls_();
                std::string cb = p_.ee(p_.ch(p_.use("read1"), {N[i], sN[i], W}), C);
                return {C, ex_lemma(k, [&, i, C, cb, wb](const Rec& R) {
                            std::string r1 = p_.ch(cb, {R.r, R.sr, N[k], R.tr, R.ys[i], R.sy[i], R.pm[i]});
                            std::string b = p_.ch(wb, {R.ys[i], R.sy[i]});
                            return iff_trans(r1, b, elem(R.r, C), "zero(" + R.ys[i] + ")");
                        })};
            }
            if (op == "snoc") {
                std::string W = witness("S").first;
                std::vector<size_t> ix;
                for (const auto& a : f->args) ix.push_back(idx.at(a));
                std::string C = cls_();
                std::string cb = p_.ee(p_.ch(p_.use("read4"), {N[ix[0]], sN[ix[0]], N[ix[1]], sN[ix[1]], N[ix[2]],
                                                               sN[ix[2]], N[ix[3]], sN[ix[3]], W}),
                                       C);
                return {C, ex_lemma(k, [&, ix, C, cb](const Rec& R) {
                            std::vector<std::string> args = {R.r, R.sr, N[k], R.tr}, bargs;
                            std::string ys;
                            for (size_t i : ix) {
                                args.insert(args.end(), {R.ys[i], R.sy[i], R.pm[i]});
                                bargs.insert(bargs.end(), {R.ys[i], R.sy[i]});
                                ys += (ys.empty() ? "" : ", ") + R.ys[i];
                            }
                            return iff_trans(p_.ch(cb, args), p_.ch(rsk_, bargs), elem(R.r, C), "snoc(" + ys + ")");
                        })};
            }
            throw Refused("the atom " + print(f));
        }

        if (f->k == K::False) {
            std::string C = N[0];
            return {C, ex_lemma(k, [&, C](const Rec& R) {
                        std::string hr = p_.assume(elem(R.r, C));
                        std::string f1 = p_.ii(p_.ne(p_.ch(zdef_, {R.r, R.sr}), hr));
                        std::string g1 = p_.ii(p_.be(p_.assume("false"), elem(R.r, C)));
                        return p_.iff(f1, g1);
                    })};
        }

        if (f->k == K::Pred) {
            auto kid = gen(t.kids[0]);
            std::string Cc = kid.first, exc = kid.second;
            std::string pdef = p_.use(defs_.at(f->name).axiom);
            return {Cc, ex_lemma(k, [&, Cc, exc, pdef](const Rec& R) {
                        std::map<std::string, std::string> m;
                        for (size_t i = 0; i < t.scope.size(); ++i) m[t.scope[i]] = R.ys[i];
                        std::vector<std::string> args;
                        for (const auto& a : f->args) args.push_back(m.count(a) ? m[a] : a);
                        std::string inst = p_.ch(pdef, args);
                        std::string e1 = p_.ch(exc, R.args());
                        std::string f1 = p_.ii(p_.ier(inst, p_.iel(e1, p_.assume(elem(R.r, Cc)))));
                        std::string g1 = p_.ii(p_.ier(e1, p_.iel(inst, p_.assume(print(atom(f->name, args))))));
                        return p_.iff(f1, g1);
                    })};
        }

        if (f->k == K::Not) {
            auto kid = gen(t.kids[0]);
            std::string Ca = kid.first, exa = kid.second;
            std::string C = cls_();
            std::string cb = p_.ee(p_.ch(p_.use("B3"), {Ca}), C);
            return {C, ex_lemma(k, [&, C, Ca, exa, cb](const Rec& R) {
                        return cong_not(p_.ch(cb, {R.r, R.sr}), p_.ch(exa, R.args()), elem(R.r, C), elem(R.r, Ca),
                                        text_at(t.kids[0], R.ys));
                    })};
        }

        if (f->k == K::And || f->k == K::Or || f->k == K::Imp || f->k == K::Iff) {
            auto ka = gen(t.kids[0]);
            auto kb = gen(t.kids[1]);
            std::string Ca = ka.first, exa = ka.second, Cb = kb.first, exb = kb.second;
            std::string row = f->k == K::And ? "B2" : f->k == K::Or ? "B_or" : f->k == K::Imp ? "B_imp" : "B_iff";
            std::string C = cls_();
            std::string cb = p_.ee(p_.ch(p_.use(row), {Ca, Cb}), C);
            return {C, ex_lemma(k, [&, C, Ca, Cb, exa, exb, cb](const Rec& R) {
                        std::string rb = p_.ch(cb, {R.r, R.sr});
                        std::string ea = p_.ch(exa, R.args()), eb = p_.ch(exb, R.args());
                        return cong(f->k, rb, ea, eb, elem(R.r, C), elem(R.r, Ca), elem(R.r, Cb),
                                    text_at(t.kids[0], R.ys), text_at(t.kids[1], R.ys));
                    })};
        }

        // All and Ex: the bound variable has index k, its record the snoc of r at N_k.
        bool ex = f->k == K::Ex;
        auto kid = gen(t.kids[0]);
        std::string Cc = kid.first, exc = kid.second;
        std::string C = cls_();
        std::string cb = p_.ee(p_.ch(p_.use(ex ? "row_ex" : "row_all"), {N[k], sN[k], Cc}), C);
        // elem(b, Cc) <-> psi'(y, v), for b the snoc of r at N_k with v
        auto at_snoc = [&, k, exc](const Rec& R, const std::string& v, const std::string& sv, const std::string& b,
                                   const std::string& sb, const std::string& sn) {
            std::string sf = p_.ch(snoc_facts_, {N[k], sN[k], N[k + 1], sN[k + 1], ns_[k], R.r, v, sv, b, R.tr, sn});
            Rec B;
            B.r = b;
            B.sr = sb;
            B.tr = p_.al(sf);
            std::string pv = p_.al(p_.ar(sf)), keep = p_.ar(p_.ar(sf));
            for (size_t i = 0; i < k; ++i) {
                B.ys.push_back(R.ys[i]);
                B.sy.push_back(R.sy[i]);
                B.pm.push_back(p_.ch(keep, {N[i], R.ys[i], R.pm[i]}));
            }
            B.ys.push_back(v);
            B.sy.push_back(sv);
            B.pm.push_back(pv);
            return p_.ch(exc, B.args());
        };
        return {C, ex_lemma(k, [&, ex, C, cb, at_snoc](const Rec& R) {
                    std::string rb = p_.ch(cb, {R.r, R.sr});
                    if (ex) {
                        std::string v = eigen_();
                        std::string e = p_.ee(p_.iel(rb, p_.assume(elem(R.r, C))), v, true);
                        std::string sv = p_.al(e);
                        std::string b = eigen_();
                        std::string e2 = p_.ee(p_.ar(e), b, true);
                        std::string sb = p_.al(e2), sn = p_.al(p_.ar(e2)), bin = p_.ar(p_.ar(e2));
                        std::string body = p_.iel(at_snoc(R, v, sv, b, sb, sn), bin);
                        std::string f1 = p_.ii(p_.ei(p_.ei(p_.ei(p_.ai(sv, body), v))));
                        std::string h2 = p_.assume(text_at(t, R.ys));
                        v = eigen_();
                        e = p_.ee(h2, v, true);
                        sv = p_.al(e);
                        std::string body2 = p_.ar(e);
                        b = eigen_();
                        e2 = p_.ee(p_.ch(snoc_ex_, {R.r, R.sr, N[k], sN[k], v, sv}), b, true);
                        sb = p_.al(e2);
                        sn = p_.ar(e2);
                        bin = p_.ier(at_snoc(R, v, sv, b, sb, sn), body2);
                        std::string w = p_.ei(p_.ai(sv, p_.ei(p_.ai(sb, p_.ai(sn, bin)), b)), v);
                        std::string g1 = p_.ii(p_.ei(p_.ei(p_.ier(rb, w))));
                        return p_.iff(f1, g1);
                    }
                    std::string ra = p_.iel(rb, p_.assume(elem(R.r, C)));
                    std::string v = eigen_();
                    p_.fix(v);
                    std::string sv = p_.assume("set(" + v + ")");
                    std::string b = eigen_();
                    std::string e2 = p_.ee(p_.ch(snoc_ex_, {R.r, R.sr, N[k], sN[k], v, sv}), b, true);
                    std::string sb = p_.al(e2), sn = p_.ar(e2);
                    std::string bin = p_.ch(ra, {v, sv, b, sb, sn});
                    std::string body = p_.iel(at_snoc(R, v, sv, b, sb, sn), bin);
                    std::string f1 = p_.ii(p_.fi(p_.ii(p_.ei(body))));
                    std::string h2 = p_.assume(text_at(t, R.ys));
                    v = eigen_();
                    p_.fix(v);
                    sv = p_.assume("set(" + v + ")");
                    b = eigen_();
                    p_.fix(b);
                    sb = p_.assume("set(" + b + ")");
                    sn = p_.assume("snoc(" + R.r + ", " + N[k] + ", " + v + ", " + b + ")");
                    std::string bin2 = p_.ier(at_snoc(R, v, sv, b, sb, sn), p_.ch(h2, {v, sv}));
                    std::string x = p_.fi(p_.ii(p_.fi(p_.ii(p_.ii(bin2)))));
                    std::string g1 = p_.ii(p_.ier(rb, x));
                    return p_.iff(f1, g1);
                })};
    }
};

}  // namespace

Output construct(const Request& req, const std::map<std::string, Def>& defs) {
    Machine m(defs, req.params);
    return m.run(req);
}

}  // namespace cls
