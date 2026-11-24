# The class machine

The class machine writes NBG's class existence one formula at a time: given a fol-zfc formula φ and the variables it
abstracts, a claim that the class of φ exists, and its proof in plain fol-zfc steps, checked by
`//src/tools:proof_checker` over the library in `lib/`. isa2fol writes the same claims for formulas that come from
Isabelle terms (`Sources/Lowering/Classes.swift`); the machine writes them for every other formula.

## 1. Why

`forall_elim` instantiates only at a variable and the language has no function symbols, so a theorem over a class
(`Nat.nat_induct`, `Fixedpt.coinduct`, `separation`, `replacement`) is cited at a formula φ only through a variable for
`{x⃗ | φ}`. Class existence is a schema in NBG: one proof per formula, by induction on φ (isa2fol `docs/FOUNDATION.md`
§3).

| Client | Needs a class for |
|---|---|
| sys2fol's proof compiler | each invariant and each induction predicate it writes |
| rtl2fol | each latch equation's induction on time |
| ai-fol | a cite at a formula; a witness defined by a formula |
| `math/` | each library theorem cited at a formula |

## 2. Request

- φ, a formula in `src/core`'s formula IR.
- The shape wanted (§4). GRAPH's bound is no part of the request: its claim holds for every set D.
- x⃗, the abstracted variables in order: the class's arity k.
- p⃗, φ's other free variables, the parameters: each a set (under `set(p)`) or a class.
- The loaded library parts, for the constants and `@def`s φ mentions and the rows it is read through.

A ROW request is φ over its places x⃗, one to four of them, with no parameters: it asks for φ's row (§4).

## 3. The construction

FOUNDATION §3: a subformula's assignments range over the variables in scope at it, numbered `0, 1, …` as they come into
scope (x⃗ first, then each bound variable at its quantifier), so every domain is a natural number and `∃` removes the
largest index. An atom is read as membership of its entries in its witness class. Every row is a claim of
`lib/base/tiers/classes` or `lib/base/tiers/logic`, proved from B1–B7.

| Construct | Witness class | Row |
|---|---|---|
| `elem(x, y)` | B1's `E` | `read2` |
| `eq(x, y)` | `cls_diag` | `read2` |
| `elem(x, Y)`, Y a parameter | Y | `read1` |
| `zero(x)`, `nsucc(n, m)`, `snoc(t, n, v, s)` | `cls_zero`, `cls_nsucc`, `cls_snoc4` | `read1`, `read2`, `read4` |
| a library constant applied, `c(x⃗, y)` | c's class | the argument tuple read by `TUPLE_ROW_n` |
| a subformula that is an instance of a loaded row's formula | the row's class | `read1`, `read2` or `read4` at its places' entries |
| a `@def` predicate of one to four places, none of them a parameter, with no row loaded | a row made in the proof | the same |
| any other `@def` predicate | | its body, unfolded |
| `φ ∧ ψ`, `¬φ`, `φ → ψ` | | `B2`, `B3`, `B_imp` |
| `φ ∨ ψ`, `φ ↔ ψ` | | rewritten to ∧, ¬ and →, the equivalence proved in the steps |
| `∃v. set(v) ∧ φ`, `∀v. set(v) → φ` | | `row_ex`, `row_all` |
| the domain | | `tuples_class`, intersected once at the top |

Refused at the gate: a quantifier without its `set` guard (it ranges over classes, and class existence holds only for
formulas quantifying over sets); a class parameter anywhere but a membership's right side; a `@def` that reaches itself.

`TUPLE_ROW_n` is in the pinned unit (`IFOL`) for the arities isa2fol needed; the machine cites it there and writes its
own for any other arity.

A row is found among the loaded claims by its statement (§4), whatever its name: the machine's own rows (`rows/`), a
library's, and any claim of the form, as `cls_zero` and `g5_rot` are. A row made in the proof is made once, before the
classes that read it: a defined predicate's, for its definition, and one for each subformula of one to four places whose
occurrences cost more lines than the row and its reads, by the machine's count of its own lines, the one saving most
first.

The proof is written in two passes. Every node's class is made first, at the proof's top, children before parents. Then
φ is proved in one scope, at a record of its variables, each node's `elem(r, C) ↔ ψ` from its children's by a schema
proved once in the machine's package (`rows/steps`): base's `iff_trans` for an atom and a read, `node_not`, `node_and`,
`node_or`, `node_imp` and `node_iff` for a connective, `node_ex` and `node_all` for a quantifier. A quantifier proves its
body in place, at every extension of the record by one entry, with the facts of only the entries its body reads. The
writer writes each `use` once a proof, and a step of the same text as one written in a scope still open is that step.

## 4. Output

Every output is a proved `∃` claim: a class enters a client's proof by `exists_elim` on it, never by a definition.
Written for k = 1; for k > 1, ⟨x⟩ is the tuple of x⃗, and `pmem(z, x, a)` is one hypothesis per index of a `zero`,
`nsucc` chain.

| Written | In fol-zfc |
|---|---|
| a is ⟨x⟩ | `∀z. set(z) → (zero(z) → snoc(z, z, x, a))` |
| a's entry at index i is y | `pmem(i, y, a)` |
| a is a tuple of length n | `tuple(a, n)` |

**CLASS**, the form of isa2fol's `CLASS_` claims, so the two are interchangeable:

```
∀p⃗. ∃C. ∀a. set(a) → (elem(a, C) ↔ ∃x. set(x) ∧ a is ⟨x⟩ ∧ φ(x, p⃗))
```

**EXACT**, the form of `read1` and `TUPLE_ROW_n`, indices before `∃C`: a citation reads `⟨n⟩ ∈ C ↔ φ(n)` either way,
with no injectivity of tuples and no congruence of φ.

```
∀p⃗. ∀z. set(z) → (zero(z) → ∀o. set(o) → (nsucc(z, o) →
  ∃C. ∀a. set(a) → (tuple(a, o) → ∀x. set(x) → (pmem(z, x, a) → (elem(a, C) ↔ φ(x, p⃗))))))
```

**VAL**, a class of values, from EXACT by the base schema `member_class` (`lib/base/tiers/metafun`):

```
∀p⃗. ∃A. ∀u. set(u) → (elem(u, A) ↔ φ(u, p⃗))
```

`elem_first_subst` at A is φ's congruence in u, so a client holding VAL needs no congruence proof of φ.

**SET**, a set defined by φ inside a set B, from VAL by `separation`:

```
∀p⃗. ∀B. set(B) → ∃s. set(s) ∧ ∀u. set(u) → (elem(u, s) ↔ elem(u, B) ∧ φ(u, p⃗))
```

**ROW**, φ over its places x⃗ read through one class W by `read1`, `read2` or `read4` (a third place read twice):

```
∃W. ∀u. set(u) → (elem(u, W) ↔ φ(u))
∃W. ∀u v. set(u) → set(v) → (pmem(u, v, W) ↔ φ(u, v))
∃W. ∀u v w x. set(u) → … → ((∃p q. kpair(v, w, p) ∧ kpair(p, u, q) ∧ pmem(q, x, W)) ↔ φ(u, v, w[, x]))
```

Its proof: φ's tuples as pairs, a VAL class by `member_class`, and the iff, carried between equal places by φ's class
at a record that holds them, `g2_pmem_cong` moving each entry.

**GRAPH**, the operator `X ↦ {u ∈ D | φ(u, X, p⃗)}` as the class `ZF.Fixedpt` applies (`function`, and `apply` at ⟨X⟩):

```
∀p⃗. ∀D. set(D) → ∃G. function(G) ∧ ∀X. set(X) → ∀t. set(t) → (t is ⟨X⟩ →
  ∀r. set(r) → (apply(t, r, G) ↔ ∀u. set(u) → (elem(u, r) ↔ elem(u, D) ∧ φ(u, X, p⃗))))
```

From the two-variable EXACT of `∃X. t is ⟨X⟩ ∧ ∀X'. t is ⟨X'⟩ → r = Φ(X')` by the base schema `graph_class`, the form
`ZF.Fixedpt`'s own graphs take; `function(G)` by `extensionality`; `apply` agrees with the graph by `apply_pmem`, as
SET gives every X a value, and the VAL of `X' ↦ r = Φ(X')` carries r from X to X'.

A claim is named `Cls.<SHAPE>_<fp>`, `<fp>` a hash of its whole statement, so two claims with one name have one
statement: the checker drops a claim whose name its deps already load, without an error (`lib/README.md`), and that
drop only removes a duplicate. The `Cls.` qualifier keeps the names apart from base's, which are unqualified, and from
isa2fol's `CLASS_`. Parameters are universally quantified, so one claim serves every instance of a definition.

A claim lives in the part of the client citing it: the systems library's in its `math/` part, a spec's in its proof. A
claim many parts cite moves to a shared part.

## 5. Interface

As in ai-fol (`DECODER.md` D22): a machine takes a goal and offers one next state with the fol-zfc steps that reach it.

- **Machine:** given a goal `Γ ⊢ G` and a request, it offers `Γ, the requested shape of φ at a fresh C ⊢ G` with the
  steps. This face is the adapter every machine shares (sys2fol `DESIGN.md` §5, decision 13), built with ai-fol's
  search; the library and the command line come first.
  It is deterministic: it offers its state or refuses φ at the gate, never a wrong state, so ai-fol does not draw it as
  it draws the noisy cite and cut machines.
- **Library:** `//src/machines/class`, a request in, the claims and their steps out, in `src/proof`'s IR for a caller
  assembling a larger proof. `proof_checker` does not depend on it.
- **Command line:** `class_machine REQUEST OUT.fol.def OUT.fol.proof LIB...`. The request is lines `shape:`, `var:`,
  `params:` (each `name set` or `name class`) and `formula:`, the formula to the end of the file; the libraries are the
  parts its `@def`s and rows come from, each `@def` found among their axioms by its shape `∀x⃗. P(x⃗) ↔ body`.
  It writes the proof through the compression machine (`src/machines/compress`), over the libraries it has loaded.
  `class_claim` (`defs.bzl`) runs it at build time, its outputs a `fol_proof`'s header and proof; it loads the
  machine's rows (`//src/machines/class/rows`) unless told other rows, and a `fol_proof` of its outputs depends on them.
  `fol_group` makes several parts one dependency.

A formula outside the gate (§3) is refused with its reason: no claim and no proof. A claim is safe because
`proof_checker` checks its proof, and the machine adds no axiom.

## 6. Cost

isa2fol's class proofs: 3,502 in the pinned unit, 500–1,500 lines each for the small formulas of `ZF.Fixedpt`. A node
costs a constant; a quantifier, besides, three steps for each entry its body reads. sys2fol's 13 requests: 12,063 lines
and 379 KB once compressed, the largest, a step relation's, 5,618; the machine's 17 rows, made once, 15,542.
`proof_checker` checks the step relation's in 1.9 seconds, nearly all of it loading the libraries: a 300-line set takes
as long.

## 7. First milestone

For sys2fol's steps 4 and 5 (sys2fol `DESIGN.md` §7), every claim on `proof_checker`'s Proved list:

1. The formula of a `CLASS_` claim isa2fol proved, its CLASS and EXACT checked side by side with isa2fol's.
2. Step 4's set J, the implementation states related to a reachable spec state, as SET: a formula through the `@def`s
   `Sys.reachable` and `Sys.related`.

Both checked: `testdata:m1` with `testdata:m1_check`, and `//math/systems:related_reachable`, whose formula unfolds to
about 570 subformulas and whose proof, 5,547 lines, checks in seconds. `testdata` also checks every shape but GRAPH,
both kinds of parameter, every connective, and the gate's refusals. The swap example's invariant and an rtl2fol latch
equation's induction predicate come with Part B and rtl2fol; GRAPH with the first use of a bridge on given systems. Not yet built, and refused for now: a
set parameter outside a membership's right side, and a library constant's atom.

## 8. To read before building

- isa2fol's `ClassProofs` (`Sources/Lowering/Classes.swift`, `Comprehension.swift`): how a library constant's atom and a
  set parameter inside a tuple atom are read, and the order of the steps.
- `src/core`'s formula IR, `src/parser`, and `src/proof`'s IR, which the machine reads and writes.
- `ZF.Fixedpt`'s proofs where they instantiate `member_class` and `graph_class`, and how `schema_inst` is written.

## 9. Not now

A `@def` with its own cached class claim, sharing claims between requests beyond identical formulas, isa2fol calling
the machine.

## 10. Decided by the user

| # | Decision | Reason |
|---|---|---|
| 1 | Five shapes, CLASS, EXACT, VAL, SET and GRAPH, each a proved `∃` claim, φ's other free variables universally quantified (§4) | A client citing a set gets it as SET, restricted from a set already there, as everything a claim is about is a set (sys2fol `DESIGN.md` §9, decision 3). A class given by a definition would be an axiom assuming its existence instead of proving it. With EXACT alone, every client would prove the other four itself. |
| 2 | The request is φ, the shape, the abstracted variables in order, the parameters each marked set or class, and the loaded parts (§2). A formula outside the gate is refused with its reason. The library and the command line first; the machine face once the shared machine interface is decided (§5) | A claim is safe because the checker proved it, and the machine adds no axiom. The interface is needed before the face built on it. |
| 3 | A defined predicate is read through a row, a class proved once, as `zero`, `nsucc` and `snoc` are read; a predicate with no row the request can load gets a row made inside the request, and the request's every occurrence is read through it. A row is the claim `∃Y. ∀u. (u ∈ Y ↔ P(u))`, `∃G. ∀u v. (pmem(u, v, G) ↔ P(u, v))` or `∃R. ∀u v w x. ((∃p q. kpair(v, w, p) ∧ kpair(p, u, q) ∧ pmem(q, x, R)) ↔ P(u, v, w))` (the last for four places with `P(u, v, w, x)`), read by `read1`, `read2` or `read4`; the request `shape: ROW` makes one (the user, 2026-11-23, after the machine's output was measured) | 95% of the machine's lines came from unfolding `tuple` and `pmem` at every occurrence, at the depth of each; rows cut an estimated 16× of all of them, and no predicate is unfolded per occurrence any more. |
| 4 | A row is found among the loaded claims by its statement, whatever its name, and named by its statement's hash, `Cls.ROW_…`, like every claim the machine writes (the user, 2026-11-23) | No names to keep; a row proved another way is found too; it is checked like any claim, so how it was proved does not matter. |
| 5 | The rows of the foundation's predicates live in the machine's package and are loaded for every request; a library's rows ship with that library's definitions (the user, 2026-11-23) | No client lists rows, so none is forgotten; the foundation is not edited. |
| 6 | A formula's stretches between quantifiers are each proved in one scope: every node's class is made first, at the proof's top; then each stretch's iffs are proved for one record of its length, its quantifiers' bodies proved before it as stretches of their own and cited at the records the quantifiers extend (agreed by the user, 2026-11-23) | Two thirds of the machine's lines re-introduced a record's variables at every node and cited each child's lemma at them; one scope per stretch leaves that only to the quantifiers, an estimated 1.8× fewer lines. |
| 7 | A row reads any formula, not only a defined predicate: its claim states the reading form at its places ↔ a formula ψ of them, and the machine reads any subformula that is an instance of a loaded row's ψ, bound variables renamed. A ROW request names ψ over its places. The machine's package holds rows for the tuple encoding's chains as sys2fol's writer writes them: the numerals 1 to 4, a tuple's entries 0 to 3, and records of one to three entries (decided by the user, 2026-11-23, who waived the check for changes that only shape the machine's proofs) | The writer's chains were most of the remaining quantifier nodes: with decision 6, sys2fol's 13 requests went from 78,387 lines to 37,073. A foundation lemma of a row's form, such as `cls_zero` or `g5_rot`, is read as a row too. |
| 8 | A quantifier's body is proved in place, at every extension of its record by one entry, once for both directions of its iff, with the facts of only the entries the body reads, in place of decision 6's lemma per stretch; a row is made in the request for each subformula of one to four places whose occurrences cost more lines than the row and its reads (decided by the user, 2026-11-23, under decision 7's waiver) | A quantifier cost about 100 lines and 12 for each variable in scope, and costs about 80 and 3 for each entry its body reads: sys2fol's 13 requests went from 37,073 lines to 20,961, a step relation's set from 22,504 to 10,527. |
| 9 | A node's iff follows from its children's by a schema proved once in the machine's package (`rows/steps`), cited by one instantiation, in place of the derivation written out at each node; the writer writes each `use` once a proof, and a step of the same text as one written in a scope still open is that step (the user, 2026-11-24: "always try our best to make the proof size small") | sys2fol's 13 requests went from 20,961 lines to 12,168 and from 994 KB to 669 KB, the step relation's set from 10,527 lines to 5,665. |
