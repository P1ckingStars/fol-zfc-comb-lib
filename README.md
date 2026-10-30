# First-Order Logic Theorem Prover with ZFC

A natural deduction theorem prover for first-order logic with ZFC set theory axioms, written in C++.

## Features

- **First-Order Logic**: Full support for universal and existential quantifiers
- **ZFC Set Theory**: Isabelle/ZF translated over an NBG foundation, conservative over ZFC (`lib/README.md`)
- **Formula Parser**: Flex/Bison parser supporting multiple syntax styles
- **Natural Deduction**: Complete rule set including classical logic (excluded middle, double negation elimination)
- **Proof Scripts**: Write and verify proofs in `.fol.def` / `.fol.proof` files
- **Definition Annotations**: `@def(predicate)` marks axioms as definitions and prevents redefinition
- **Bazel Proof Verification**: Custom Bazel rules for incremental proof checking with dependency tracking
- **Equality**: Axiomatized in pure FOL by `extensionality` and `elem_first_subst`; substitution goes through lemmas such as `elem_second`

## Building

Requires Bazel 7+, C++20 compiler, flex, and bison.

```bash
# Run all tests
bazel test //test:all_tests

# Or run individual test suites
bazel test //test:core_test       # Core logic tests
bazel test //test:runtime_test    # Runtime and proof execution tests

# Verify proofs via Bazel
bazel build //lib:base            # Check the NBG foundation
bazel build @zf//:parts           # Check the whole translated library
bazel build //math/...            # Check new mathematics and the parts it cites
```

## Formula Syntax

### Propositional Connectives

| Connective | Symbols |
|------------|---------|
| Negation | `~`, `!`, `not` |
| Conjunction | `&`, `and` |
| Disjunction | `\|`, `or` |
| Implication | `->`, `implies` |
| Biconditional | `<->`, `iff` |
| Bottom | `false`, `_\|_` |

### Quantifiers

| Quantifier | Syntax |
|------------|--------|
| Universal | `forall x. P(x)` |
| Existential | `exists x. P(x)` |

### Predicates

```
P(x)           # Unary predicate
R(x, y)        # Binary predicate
elem(x, y)     # Set membership (x in y)
eq(x, y)       # Equality
```

Precedence (lowest to highest): `<->` < `->` < `|` < `&` < `~` < quantifiers

## File Format

Definitions and proofs are split into two file types:

### `.fol.def` — Definitions (axioms + claims)
```fol
include "axioms.fol.def"

# Definition axioms — @def(predicate) prevents redefining the same predicate
@def(singleton) axiom singleton_def: forall s. forall x. (singleton(s, x) <-> ...)

# Plain axioms (no @def annotation)
axiom extensionality: forall x. forall y. (...)

# Claims (must be proved in the .fol.proof file)
claim eq_refl: forall x. eq(x, x)
```

### `.fol.proof` — Proofs
```fol
proof eq_refl:
    fix x
    # ... proof steps ...
    qed h
```

### Legacy `.fol` — Combined format
Single files containing axioms, claims, and proofs together (still supported).

## Proof Script Syntax

```fol
axiom all_P: forall x. P(x)
axiom all_P_impl_Q: forall x. (P(x) -> Q(x))
claim all_Q: forall x. Q(x)

proof all_Q:
    fix x                           # Introduce eigenvariable
    h1 = use all_P                  # Get axiom as premise
    h2 = forall_elim h1, x          # Instantiate with fixed var
    h3 = use all_P_impl_Q
    h4 = forall_elim h3, x
    h5 = implies_elim h4, h2        # Modus ponens
    h6 = forall_intro h5            # Generalize over x
    qed h6
```

### Statement Types

| Statement | Description |
|-----------|-------------|
| `axiom name: φ` | Declare an axiom (assumed true) |
| `@def(P) axiom name: φ` | Declare a definition axiom for predicate `P` (prevents redefining `P`) |
| `claim name: φ` | Declare a claim (must be proved) |

### Proof Steps

| Step | Description |
|------|-------------|
| `fix x` | Introduce eigenvariable for universal intro/existential elim |
| `h = use name` | Get axiom or proven theorem as premise |
| `h = assume φ` | Assume formula (for implies_intro, not_intro) |
| `h = let φ` | Create formula handle without deriving (for or_intro, bottom_elim) |
| `h = rule args` | Apply inference rule |
| `qed h` | Complete proof with final step |

### Inference Rules

**Propositional:**

| Rule | Syntax | Description |
|------|--------|-------------|
| And-Intro | `and_intro h1, h2` | `A, B => A & B` |
| And-Elim | `and_elim_l h` / `and_elim_r h` | `A & B => A` or `B` |
| Or-Intro | `or_intro_l h1, h2` / `or_intro_r h1, h2` | `A => A \| B` (h2 is `let`) |
| Or-Elim | `or_elim h, h1, h2` | Case split: `A\|B, A->C, B->C => C` |
| Implies-Intro | `implies_intro h` | Discharge assumption: `[A]...B => A->B` |
| Implies-Elim | `implies_elim h1, h2` | Modus ponens: `A->B, A => B` |
| Not-Intro | `not_intro h` | `[A]..._\|_ => ~A` |
| Not-Elim | `not_elim h1, h2` | `~A, A => _\|_` |
| Iff-Intro | `iff_intro h1, h2` | `A->B, B->A => A<->B` |
| Iff-Elim | `iff_elim_l h1, h2` / `iff_elim_r h1, h2` | Extract direction from biconditional |
| Bottom-Elim | `bottom_elim h1, h2` | Ex falso: `_\|_, φ => φ` (h2 is `let`) |

**First-Order:**

| Rule | Syntax | Description |
|------|--------|-------------|
| Forall-Intro | `forall_intro h` | Close fix scope: `[x]...P(x) => forall x. P(x)` |
| Forall-Elim | `forall_elim h, t` | Instantiate: `forall x. P(x) => P(t)` |
| Exists-Intro | `exists_intro h` | Generalize: `P(t) => exists x. P(x)` |
| Exists-Elim | `exists_elim h` | Open witness scope from `exists x. P(x)` |

**Equality & Classical:**

| Rule | Syntax | Description |
|------|--------|-------------|
| Double-Neg-Elim | `double_neg_elim h` | `~~A => A` |
| Excluded-Middle | `excluded_middle h` | `=> A \| ~A` (h is `let`) |

## Project Structure

```
src/
├── core/
│   ├── formula.h/.cpp    # Formula AST and database
│   └── proof.h           # Proof construction and steps
├── parser/
│   ├── formula.l         # Flex lexer specification
│   ├── formula.y         # Bison parser specification
│   ├── formula_ast.h     # Parser AST nodes
│   ├── parser.h          # Parser API
│   └── parser_bison.cpp  # AST to formula conversion
├── runtime/
│   └── runtime.h/.cpp    # Runtime and ProofContext classes
├── tools/
│   └── proof_checker.cpp # Standalone proof verification binary
├── util/
│   ├── registry.h        # Arena-style registry for formulas
│   ├── error.h           # Error handling utilities
│   └── logging.h         # Logging utilities

build/
├── fol.bzl               # Bazel rules: fol_library, fol_proof, fol_group
└── fol_unit.bzl          # Repository rule: a translated unit as fol_proof targets

lib/
├── README.md             # What the library is, how to read it, how to re-pin it
├── base/                 # NBG foundation: the 19 axioms and 13 tiers (from isa2fol)
└── zf.sha256             # Pin of the translated unit, which stays out of git

math/                     # New mathematics, built on the library

test/
├── core_test.cpp         # Core logic tests
├── runtime_test.cpp      # Runtime and proof execution tests
└── corpus/               # The hand-written proofs the library replaced; a regression corpus
```

## Axioms

Single-sorted NBG with global choice, conservative over ZFC: 19 axioms in `lib/base/axioms.fol.def`.

- **Encoding** — `members_are_sets`, `elem_first_subst`
- **Extensionality** — As a biconditional
- **Class existence** — Goedel's `B1`-`B7`
- **Set existence** — `empty`, `pairing`, `union`, `power`, `infinity`, `replacement`, `separation`
- **Regularity** — Mendelson's axiom D
- **Choice** — Goedel's axiom E

## Examples

### Simple: Modus Ponens

```fol
axiom all_P: forall x. P(x)
axiom all_P_impl_Q: forall x. (P(x) -> Q(x))
claim all_Q: forall x. Q(x)

proof all_Q:
    fix x
    h1 = use all_P
    h2 = forall_elim h1, x
    h3 = use all_P_impl_Q
    h4 = forall_elim h3, x
    h5 = implies_elim h4, h2
    h6 = forall_intro h5
    qed h6
```

### Unfolding Definitions

Proofs often unfold definitions via `iff_elim`, apply reasoning, then fold back:

```fol
# Definitions use @def to prevent accidental redefinition
@def(rel_elem) axiom rel_elem_def: forall f. forall a. forall b.
    (rel_elem(f, a, b) <-> exists p. (pair(p, a, b) & elem(p, f)))
@def(in_domain) axiom domain_def: forall f. forall a.
    (in_domain(f, a) <-> exists b. rel_elem(f, a, b))

# Prove: rel_elem implies in_domain
claim domain_elem: forall f. forall a. forall b.
    (rel_elem(f, a, b) -> in_domain(f, a))

proof domain_elem:
    fix f
    fix a
    fix b
    h_rel = assume rel_elem(f, a, b)
    ddef = use domain_def
    ddef1 = forall_elim ddef, f
    ddef2 = forall_elim ddef1, a
    h_ex = exists_intro h_rel, b          # exists b. rel_elem(f, a, b)
    h_dom = iff_elim_r ddef2, h_ex        # fold back to in_domain(f, a)
    h_impl = implies_intro h_dom
    h3 = forall_intro h_impl
    h2 = forall_intro h3
    h1 = forall_intro h2
    qed h1
```

### Equality Substitution

There is no built-in substitution rule. Equality is axiomatized by `extensionality` and `elem_first_subst` (`lib/base/axioms.fol.def`), and substitution goes through lemmas: `elem_first_subst` and `elem_second` for each position of `elem`, `set_cong` for `set`. A proof about a defined predicate unfolds its `@def` axiom, substitutes inside, and folds back. This example, from `test/corpus/basics/`, substitutes through lemmas of its own:

```fol
# Prove: rel_elem is preserved under equal inputs/outputs

proof rel_elem_eq:
    fix f
    fix a
    fix b
    fix c
    fix d
    h = assume rel_elem(f, a, b) & eq(a, c) & eq(b, d)
    # ... extract h_rel, h_eq_ac, h_eq_bd ...
    rdef = use rel_elem_def
    # Unfold rel_elem(f, a, b) to exists p. (pair(p, a, b) & elem(p, f))
    h_ex = iff_elim_l rdef3, h_rel
    h_wit = exists_elim h_ex, w
    h_pair_ab = and_elim_l h_wit
    h_elem_wf = and_elim_r h_wit
    # pair_eq_a: eq(a, c) & pair(w, a, b) -> pair(w, c, b)
    pea = use pair_eq_a
    pea1 = forall_elim pea, w
    pea2 = forall_elim pea1, a
    pea3 = forall_elim pea2, c
    pea4 = forall_elim pea3, b
    h_pea_conj = and_intro h_eq_ac, h_pair_ab
    h_pair_cb = implies_elim pea4, h_pea_conj
    # pair_eq_b turns pair(w, c, b) into pair(w, c, d) the same way
    # Fold back to rel_elem(f, c, d)
    # ...
```

### What's Been Proved

The library holds Isabelle/ZF's theory, ordinals to integer division, translated and checked by this kernel: `lib/README.md` has the count. `math/` builds on it.

## Bazel Proof Rules

Custom Bazel rules in `build/fol.bzl` enable incremental proof verification:

```python
# Header-only target (axioms + claims, no proofs)
fol_library(
    name = "nat_lib",
    header = "nat.fol.def",
    deps = ["@zf//:ZF.Nat"],
)

# Proof verification target
fol_proof(
    name = "nat",
    header = "nat.fol.def",
    proof = "nat.fol.proof",
    deps = ["@zf//:ZF.Nat"],
)
```

Dependency chain:
```
//lib:base (fol_group) — the 19 axioms and 13 tiers
  └── @zf//:Pure, :IFOL, :FOL, :ZF.* (fol_proof) — the translated parts
        └── //math:nat (fol_proof)
```

## Regenerating Parser

After modifying `formula.l` or `formula.y`:

```bash
cd src/parser
flex --header-file=formula_lexer.h -o formula_lexer.cc formula.l
bison -d --defines=formula_parser.tab.h -o formula_parser.tab.cc formula.y
```
