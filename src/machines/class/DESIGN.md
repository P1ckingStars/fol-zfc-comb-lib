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
- The shape wanted (§4), and for GRAPH the bound D.
- x⃗, the abstracted variables in order: the class's arity k.
- p⃗, φ's other free variables, the parameters: each a set (under `set(p)`) or a class.
- The loaded library parts, for the constants φ mentions.

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
| a `@def` predicate | | its body, unfolded |
| `φ ∧ ψ`, `¬φ`, `φ → ψ` | | `B2`, `B3`, `B_imp` |
| `φ ∨ ψ`, `φ ↔ ψ` | | rewritten to ∧, ¬ and →, the equivalence proved in the steps |
| `∃v. set(v) ∧ φ`, `∀v. set(v) → φ` | | `row_ex`, `row_all` |
| the domain | | `tuples_class`, intersected once at the top |

Refused at the gate: a quantifier without its `set` guard (it ranges over classes, and class existence holds only for
formulas quantifying over sets); a class parameter anywhere but a membership's right side; a `@def` that reaches itself.

`TUPLE_ROW_n` is in the pinned unit (`IFOL`) for the arities isa2fol needed; the machine cites it there and writes its
own for any other arity.

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
  steps.
  It is deterministic: it offers its state or refuses φ at the gate, never a wrong state, so ai-fol does not draw it as
  it draws the noisy cite and cut machines.
- **Library:** `//src/machines/class`, a request in, the claims and their steps out, in `src/proof`'s IR for a caller
  assembling a larger proof. `proof_checker` does not depend on it.
- **Command line:** a request file in, a `.fol.def` and a `.fol.proof` out, for `proof_checker`.

## 6. Cost

isa2fol's class proofs: 3,502 in the pinned unit, 500–1,500 lines each for the small formulas of `ZF.Fixedpt`. Index
management is O(n) steps per quantifier (FOUNDATION §3).

## 7. First milestone

CLASS and EXACT for three formulas, every claim on `proof_checker`'s Proved list:

1. The formula of a `CLASS_` claim isa2fol proved, checked side by side with isa2fol's.
2. The swap example's invariant over `2×2`, with its SET.
3. One rtl2fol latch equation's induction predicate, with `Nat.nat_induct` cited at it.

## 8. To read before building

- isa2fol's `ClassProofs` (`Sources/Lowering/Classes.swift`, `Comprehension.swift`): how a library constant's atom and a
  set parameter inside a tuple atom are read, and the order of the steps.
- `src/core`'s formula IR, `src/parser`, and `src/proof`'s IR, which the machine reads and writes.
- `ZF.Fixedpt`'s proofs where they instantiate `member_class` and `graph_class`, and how `schema_inst` is written.

## 9. Not now

A `@def` with its own cached class claim, sharing claims between requests beyond identical formulas, isa2fol calling
the machine.
