# The library

The library is a translation: Isabelle/ZF, carried into this checker's language by `isa2fol` over an NBG foundation, and
checked here by the kernel. New mathematics goes in `math/` and cites it.

| | what | where |
|---|---|---|
| `//lib:base` | The foundation: the 19 axioms of NBG with global choice, and the 13 tiers built on them | `lib/base/`, copied unchanged from isa2fol `5dbb2a2e`; its `docs/FOUNDATION.md` is their specification |
| `@zf` | Pure, IFOL, FOL and the ZF session: 61 parts, 50,306 claims, 6,273 schemas, 3,609 of 3,616 of the session's named theorems | `~/isa2fol-units/2026-10-30_ZF/unit`, generated and 2.4 GB, so out of git; `lib/zf.sha256` pins every file |

Isabelle's other sessions (ZF-AC, ZF-Constructible, ZF-Induct, ...) are not in the library. A unit is one emission, a
lemma placed in its first citer's part, so ZF's parts in a unit holding them cite theirs: the library is its own
emission of ZF alone, not a selection from a larger unit.

## Building

`@zf` needs the unit on this machine; `FOL_UNIT` names it if it is not under `~/isa2fol-units`. `//test:all_tests` does
not need it.

```bash
bazel build //lib:base       # the foundation, in seconds
bazel build @zf//:parts      # every part, by the kernel: about 9 minutes, the parts being nearly a chain
bazel build //math/...       # new mathematics and the parts it cites
```

Each part is a `fol_proof`, so the kernel checks the library and nothing trusts a prebuilt `.fol.lib`. A change to the
kernel checks the parts a build reaches again.

## Citing it

A part is a target, named as the unit names it: `@zf//:ZF.Nat`. It brings the foundation and the parts it cites;
`@zf//:parts` is every part. A `.fol.def` in `math/` has no `include` for it: the header cites what its deps load.

```python
fol_proof(
    name = "nat",
    header = "nat.fol.def",
    proof = "nat.fol.proof",
    deps = ["@zf//:ZF.Nat"],
)
```

Theorems and constants keep Isabelle's names (`Nat.nat_succI`, `ZF_Base.succ`), and a theorem is in the part of its
theory, split as `ZF.List`, `ZF.List.2`, ... when it is large. Search the unit's `.fol.def` files for the name.

A topic is a `fol_proof` of its own, in `math/BUILD.bazel` or in a folder under `math/` with a `BUILD.bazel` holding
`package(default_visibility = ["//math:__subpackages__"])`, and cites another by naming it in `deps`. Claims, `@def`
definitions and schemas all reach the targets that depend on it. Name the parts a file cites: `ZF.Nat` loads in about 2
seconds, all of `@zf//:parts` in about 8.

## What the build does not check

A green build says every claim listed in the target's `.report` is proved from what its `deps` and header state. These
three are left to the author:

- A bare `axiom` in `math/` is accepted, and the report does not mention it. Only `lib/base/axioms.fol.def` should hold one.
- `@def` is an axiom to the kernel, which refuses a predicate defined twice but not a definition that is circular or
  otherwise inconsistent.
- A claim whose name the `deps` already load is dropped without an error: the name keeps its old statement, and the build
  passes without checking the new one. Base names are unqualified, so check the report lists the claim.

## Reading a translated statement

The language has no function symbols, so a constant is a predicate over the class it names, and each term of a
statement is a variable that predicates fix (`FOUNDATION.md`, S1). A constant `c` applied to `x⃗` is `⟨t, r⟩ ∈ C`, with
`C` its class and `t` the tuple of `x⃗`. An object variable is guarded by `set(·)`.

```fol
# 0 : nat
claim Nat.nat_0I: forall b0. (set(b0) -> (ZF_Base.zero(b0) -> (forall b1. (set(b1) -> (Nat.nat(b1) -> elem(b0, b1))))))
```

`Nat.nat(n)` says `n` is `nat`, and `ZF_Base.zero(z)` that `z` is `0`, so this reads: if `z` is `0` and `n` is `nat`, then
`z ∈ n`. A membership at a term is universal over the term's value: `x ∈ nat` is
`forall n. (set(n) -> (Nat.nat(n) -> elem(x, n)))`. The statement of `math/nat.fol.def` is written this way.

A part also holds the lemmas the translation needed, named by fingerprint: `MEET_`, `BETA_`, `SUBST_`, `ARGS_`, `CLASS_`,
`EX_`, `UNIQ_`, `FUNC_`, `TUPLE_*`, `*.BOX_*`. They are proved like the rest and can be cited; a theorem under Isabelle's
name is what to look for.

## Re-pinning

```bash
cd ~/repos/isa2fol
MEM=24G scripts/capped.sh .build/release/isa2fol lower data/zf_export \
    --skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex \
    --emit ~/isa2fol-units/DIR/unit --threads 16
MEM=16G scripts/capped.sh scripts/check-unit.sh ~/isa2fol-units/DIR/unit

cd ~/isa2fol-units/DIR/unit
sha256sum parts *.fol.def *.fol.proof > ~/repos/fol-zfc-comb/lib/zf.sha256
```

Then set `dir` in `MODULE.bazel`, and copy isa2fol's `base/` over `lib/base/` if it changed: a part is checked against
the base in this tree.

## The hand-written corpus

`test/corpus/` holds the proofs this library replaced. Nothing outside `test/` can cite them. They stay as a regression
corpus because `comb_checker`, and so `scripts/run_comb_checker.py`, has no path for a schema's proof yet, and all but
one of the translated parts hold schemas.
