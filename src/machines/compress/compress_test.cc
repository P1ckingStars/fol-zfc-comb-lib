// The machine drops what no kept step reads, reads each held fact from the step that set it, and prints what parses
// back: every block below is rewritten, the rewrite checks afresh, and each keeps the steps named.
#include <cstdio>
#include <iostream>
#include <map>
#include <sstream>
#include <string>

#include "src/machines/compress/compress.h"
#include "src/parser/parser.h"
#include "src/runtime/runtime.h"

namespace {

const char* kHeader = R"(
axiom ax_p: forall x. P(x)
axiom ax_pq: forall x. (P(x) -> Q(x))
axiom ax_e: exists x. R(x)
axiom Ax."false": forall x. P(x)
schema refl [A]: A -> A
schema allp [P(1)]: (forall x. P(x)) -> (forall x. P(x))
claim c1: forall x. Q(x)
claim c2: forall x. ((S(x) -> Q(x)) & (T(x) -> Q(x)))
claim c3: exists y. (R(y) | Q(y))
claim c4: forall x. (P(x) -> P(x))
claim c5: ((forall x. P(x)) & Q2) -> ((forall x. P(x)) & Q2)
claim c6: (~(forall x. P(x)) | (A1 <-> (B1 <-> C1))) -> (~(forall x. P(x)) | (A1 <-> (B1 <-> C1)))
claim c7: ((A1 -> B1) -> C1) -> ((A1 -> B1) -> C1)
claim c8: (exists x. (P(x) & (forall y. Q(y)))) -> (exists x. (P(x) & (forall y. Q(y))))
claim c9: forall x. P(x)
claim c10: (forall x. (P(x) & (forall x. Q(x)))) -> (forall x. (P(x) & (forall x. Q(x))))
claim c11: forall y. ((forall x. R2(x, y)) -> (forall x. R2(x, y)))
)";

// Each block, and the steps its rewrite keeps.
const std::map<std::string, size_t> kKept = {
    {"refl", 3}, {"c1", 8}, {"c2", 13}, {"c3", 7}, {"c4", 4}, {"c5", 3},
    {"c6", 3},   {"c7", 3}, {"c8", 3},  {"c9", 2}, {"allp", 3}, {"c10", 3}, {"c11", 4},
};

const char* kProof = R"(
proof refl:
    h = assume A
    i = implies_intro h
    qed i

# a dead use, a repeated use and instance, and a conjunct taken back apart
proof c1:
    fix x
    h1 = use ax_p
    h2 = forall_elim h1, x
    h3 = use ax_pq
    h4 = forall_elim h3, x
    dead = use ax_e
    h5 = implies_elim h4, h2
    h6 = use ax_p
    h7 = forall_elim h6, x
    h8 = and_intro h5, h7
    h9 = and_elim_l h8
    h10 = forall_intro h9
    qed h10

# Q(x), proved in the first case on no assumption, is still held in the second
proof c2:
    fix x
    a1 = assume S(x)
    p1 = use ax_pq
    p2 = forall_elim p1, x
    p3 = use ax_p
    p4 = forall_elim p3, x
    q1 = implies_elim p2, p4
    i1 = implies_intro q1
    a2 = assume T(x)
    r1 = use ax_pq
    r2 = forall_elim r1, x
    r3 = use ax_p
    r4 = forall_elim r3, x
    q2 = implies_elim r2, r4
    i2 = implies_intro q2
    c = and_intro i1, i2
    g = forall_intro c
    qed g

# a formula read as a payload, a witness named in it, an instance nothing reads
proof c3:
    e = use ax_e
    w = exists_elim e, y
    l = let Q(y)
    o = or_intro_l w, l
    s = schema_inst refl { A: R(y) }
    x2 = exists_intro o, y
    done = exists_intro x2
    qed done

proof c4:
    fix x
    s = schema_inst refl { A: P(x) }
    g = forall_intro s
    qed g

proof c5:
    a = assume (forall x. P(x)) & Q2
    i = implies_intro a
    qed i

proof c6:
    a = assume ~(forall x. P(x)) | (A1 <-> (B1 <-> C1))
    i = implies_intro a
    qed i

proof c7:
    a = assume (A1 -> B1) -> C1
    i = implies_intro a
    qed i

proof c8:
    a = assume exists x. (P(x) & (forall y. Q(y)))
    i = implies_intro a
    qed i

proof c9:
    h = use Ax."false"
    unused = use ax_p
    qed h

# a bound variable shadowing another, and a lambda reading a fixed variable
proof c10:
    a = assume forall x. (P(x) & (forall x. Q(x)))
    i = implies_intro a
    qed i

proof allp:
    a = assume forall x. P(x)
    i = implies_intro a
    qed i

proof c11:
    fix y
    s = schema_inst allp { P: \z. R2(z, y) }
    g = forall_intro s
    qed g
)";

std::string compress(const std::string& proof, logic::compress::Stats& stats, bool& ok) {
    logic::Runtime rt;
    ok = rt.load(kHeader).ok();
    std::string text = proof;
    std::FILE* in = fmemopen(text.data(), text.size(), "r");
    std::ostringstream out;
    auto st = logic::compress::compress(rt, in, out, stats);
    std::fclose(in);
    if (!st.ok()) std::cerr << st.error().to_string() << "\n";
    ok = ok && st.ok();
    return out.str();
}

}  // namespace

int main() {
    logic::compress::Stats stats;
    bool ok = true;
    std::string out = compress(kProof, stats, ok);
    if (!ok || stats.as_given != 0 || stats.blocks != kKept.size()) {
        std::cerr << "rewrite failed: " << stats.as_given << " of " << stats.blocks << " as given\n" << out;
        return 1;
    }
    // The rewrite checks afresh, block by block, and keeps the steps expected.
    logic::Runtime fresh;
    if (!fresh.load(kHeader).ok()) return 1;
    std::string text = out;
    std::FILE* in = fmemopen(text.data(), text.size(), "r");
    auto streamed = logic::stream_proofs(in, [&](const logic::ParsedProof& p) {
        auto st = fresh.execute_proof(p);
        if (!st.ok()) {
            std::cerr << p.claim_name << ": " << st.error().to_string() << "\n";
            ok = false;
        }
        auto want = kKept.find(p.claim_name);
        if (want == kKept.end() || want->second != p.steps.size()) {
            std::cerr << p.claim_name << ": " << p.steps.size() << " steps kept\n";
            ok = false;
        }
    });
    std::fclose(in);
    if (!streamed.ok() || !ok) {
        std::cerr << out;
        return 1;
    }
    // A rewrite is a fixed point.
    logic::compress::Stats again;
    if (compress(out, again, ok) != out || !ok) {
        std::cerr << "a second pass changed the text\n";
        return 1;
    }
    std::cout << out;
    return 0;
}
