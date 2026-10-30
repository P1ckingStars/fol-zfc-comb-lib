# FOL-ZFC: First-Order Logic Proof System with ZFC Set Theory

## Overview

A C++ implementation of a natural deduction proof system for first-order logic, with ZFC (Zermelo-Fraenkel with Choice) set theory axioms. Built with Bazel.

The library is the translated foundation: `isa2fol`'s translation of Isabelle/ZF over an NBG base (`lib/README.md`). New mathematics goes in `math/` and cites it.

## Hard rule: no string hacks in IR / system design

The IR and every pass over it must work in **structured abstract space**,
not in strings.

- Theory references must carry **typed handles** (`SentenceHandle`,
  `FormulaHandle`, `PredicateHandle`, a future `SchemaHandle`, …), not
  names. Names are a parser-input concept and a diagnostic-output concept;
  they have no place inside the IR's vocabulary.
- Identities of facts, formulas, schema instances, terms, scopes, etc.
  must be carried by registry handles or strongly-typed IR newtypes.
  Encoding identity into a string (`"@schema#5#412"`, name-mangling
  schemes, hash-into-name) is the violation pattern — refuse it.
- `unordered_map<string, …>` keyed by an IR-internal identifier is the
  same violation. Promote to `unordered_map<TypedHandle, …>`.
- The only legitimate strings in the IR are (a) `ScopeName` inside
  deferred-formula AST payloads (a parser carve-out documented in
  `src/proof/ir.h`), (b) diagnostic text in `OpHeader::loc`, and (c)
  source-cited-name fields on theory-reference ops that exist purely for
  diagnostic output and source-level dependency tracking (e.g. the
  `source_name` field on `nd::Use` / `lkr::CloseByLemma`'s axiom target —
  the dependency graph that Bazel consumes is keyed by the user-written
  source name, which can disambiguate two distinct names that intern to
  the same `SentenceHandle`). Such fields MUST NOT participate in
  identity (no `operator==`, no hashing). Anything else is a smell.
- When a pass needs to introduce new entities (e.g., synthetic
  schema-instance facts), register them in the appropriate Registry and
  use the returned handle as the identity — do not invent a name.

Apply this when designing new passes, new IR types, and when refactoring.
If the existing code uses strings where handles would do (e.g., today's
`AxiomRef { std::string name }`), the right answer is usually "tighten
the IR" rather than "match the existing convention."

## Hard rule: no corpus awareness in design

The ZFC corpus (and any other proof corpus) is **strictly a bug-catcher**.
It does NOT inform design or system development. Concretely:

- **Never** justify a design choice with "the corpus does / doesn't do X",
  "for ZFC, only Y occurs", "this case is rare in practice", or similar
  empirical-distribution arguments. These framings are disallowed.
- **Never** scope, prioritize, simplify, or omit a case based on what
  corpus proofs happen to exercise. Every case enumerated by the math
  (sound + complete spec, exhaustive variant cover, metatheorem branches)
  must be handled or explicitly rejected at an input gate — regardless of
  whether the corpus uses it.
- **Never** measure the corpus to pick between approaches. Pick on
  mathematical principle (soundness, completeness, the controlling
  theorem). The corpus has no vote.
- Corpus runs are valid **only** as a post-implementation bug-catcher:
  "the chosen design failed on input X — locate the bug." Not as an input
  to design.

Violating this rule (even with phrasing like "for the ZFC corpus this
case doesn't arise" inside a spec) is a hard error. Retract and re-derive
from the math.

## Build Commands

```bash
bazel test //test:core_test       # Core logic tests
bazel test //test:runtime_test    # Runtime and proof execution tests
bazel test //test:all_tests       # Run all tests

bazel build //lib:base            # Check the NBG foundation
bazel build @zf//:parts           # Check the whole translated library
bazel build //math/...            # Check new mathematics and the parts it cites
```

## Architecture

### Directory Structure

```
src/
├── core/                  # Core logic system
│   ├── formula.h/cpp      # Formula representation (predicates, compounds, quantifiers)
│   └── proof.h            # Natural deduction proof system and scope management
├── runtime/               # Interactive proving runtime
│   └── runtime.h/cpp      # Runtime and ProofContext classes
├── parser/                # Formula parser (Flex/Bison)
│   ├── formula.l          # Flex lexer specification
│   ├── formula.y          # Bison grammar specification
│   ├── formula_ast.h      # AST nodes for parser
│   ├── parser.h           # Parser interface (parse_formula)
│   ├── parser_bison.cpp   # AST to formula conversion
│   ├── formula_lexer.h/cc       # Pre-generated lexer
│   └── formula_parser.tab.h/cc  # Pre-generated parser
├── tools/
│   └── proof_checker.cpp  # Standalone proof verification binary
├── util/
│   ├── registry.h         # Generic registry utilities (IndexedStore, KeyedRegistry)
│   ├── error.h            # Error handling utilities
│   └── logging.h          # Logging utilities

build/
├── fol.bzl                # Bazel rules: fol_library, fol_proof, fol_group
└── fol_unit.bzl           # Repository rule: a translated unit as fol_proof targets

lib/
├── README.md              # What the library is, how to read it, how to re-pin it
├── base/                  # NBG foundation: the 19 axioms and 13 tiers (from isa2fol)
└── zf.sha256              # Pin of the translated unit, which stays out of git

math/                      # New mathematics, built on the library

test/
├── core_test.cpp          # Core logic tests
├── runtime_test.cpp       # Runtime and proof execution tests
└── corpus/                # The hand-written proofs the library replaced; a regression corpus nothing outside test/ can cite
```

### Key Types (core/)

**formula.h:**
- `FormulaHandle`, `PredicateHandle`, `SentenceHandle` - Handle types for registry items
- `var_index` - De Bruijn-style variable index (0 = x, 1 = y, etc.)
- `Term` - A variable (generalized or fixed)
- `Formula` - Variant: `PredicateInstance`, `Compound`, `Quantified`
- `Op` - Operators: And, Or, Implies, Iff, Not, Bottom, Forall, Exists
- `GlobalContext` - Central storage for all formulas, predicates, sentences, and definition tracking

**proof.h:**
- `FormulaHandle` - Reference to a formula in a proof
- Natural deduction rules (and_intro, implies_elim, forall_intro, etc.)
- RAII scope management for assumptions and eigenvariables

**runtime/runtime.h:**
- `Runtime` - Stores axioms/theorems as strings, creates proof contexts
- `ProofContext` - Isolated proof environment with local ProofDatabase
  - `use(name)` - Get premise step for axiom/theorem
  - `parse(str)` - Parse formula into local db
  - `used()` - Get set of all axioms/theorems used
  - `qed()` - Complete proof and register theorem

## Natural Deduction Rules

### Propositional
- **Conjunction**: `and_intro`, `and_elim_l`, `and_elim_r`
- **Disjunction**: `or_intro_l`, `or_intro_r`, `or_elim`
- **Implication**: `implies_intro` (discharges assumption), `implies_elim` (modus ponens)
- **Negation**: `not_intro` (from bottom), `not_elim` (produces bottom)
- **Bottom**: `bottom_elim` (ex falso quodlibet)
- **Biconditional**: `iff_intro`, `iff_elim_l`, `iff_elim_r`

### First-Order
- **Universal**: `forall_intro` (requires eigenvariable), `forall_elim` (instantiate)
- **Existential**: `exists_intro`, `exists_elim` (requires eigenvariable)

### Equality
- **Symmetry**: `eq_sym` (from `eq(a,b)`, derive `eq(b,a)`). The ND→LKR translator rejects it, so proofs use the `eq_symm` lemma instead.
- **Substitution**: no built-in rule; see [Substituting Equals](#substituting-equals).

## Parser (Flex/Bison)

Pre-generated files in `src/parser/`. To regenerate after editing `.l` or `.y`:

```bash
cd src/parser
flex --header-file=formula_lexer.h -o formula_lexer.cc formula.l
bison -d --defines=formula_parser.tab.h -o formula_parser.tab.cc formula.y
```

### Syntax

```
Atoms:       A, B, P(x), R(x,y), _|_ (bottom), false
Negation:    ~A, !A, not A
Binary:      A & B, A | B, A -> B, A <-> B
             and, or, implies, iff (keyword alternatives)
Quantified:  forall x. P(x), exists x. P(x)
Iota terms:  P((iota x. Q(x)))  — definite description as predicate argument
Statements:  axiom name: φ, claim name: φ, @def(P) axiom name: φ
```

### Precedence (lowest to highest)
1. `<->` (iff) - left associative
2. `->` (implies) - right associative
3. `|` (or) - left associative
4. `&` (and) - left associative
5. `~`, `forall`, `exists` - unary/quantifiers
6. atoms, parentheses

## Axioms

Single-sorted NBG: variables range over classes, and a set is a class satisfying `set(x)`. Predicates: `elem(x, y)` (membership), `eq(x, y)` (equality), `set(x)`.

The 19 axioms are in `lib/base/axioms.fol.def`:
1. **`members_are_sets`**, **`elem_first_subst`** - Encoding hygiene (2 axioms)
2. **`extensionality`** - Classes equal iff same members, as a biconditional
3. **`B1`-`B7`** - Goedel's class existence, the finite replacement for comprehension
4. **`empty`**, **`pairing`**, **`union`**, **`power`**, **`infinity`**, **`replacement`**, **`separation`** - Set existence
5. **`regularity`** - Mendelson's axiom D
6. **`choice`** - Goedel's axiom E, global choice

NBG with global choice is conservative over ZFC, so a proof from these witnesses a theorem of ZFC. `math/` adds `@def` definitions and claims, never a bare `axiom`.

## File Format: .fol.def / .fol.proof Split

Axioms and claims live in `.fol.def` header files. Proofs live in `.fol.proof` files. This separation enables Bazel-based proof verification.

### .fol.def (Header files)
```fol
include "axioms.fol.def"

# Definition axioms — @def(predicate) prevents redefining the same predicate
@def(singleton) axiom singleton_def: forall s. forall x. (singleton(s, x) <-> ...)

# Plain axioms (no @def annotation)
axiom extensionality: forall x. forall y. (...)

# Claims (to be proved in the .fol.proof file)
claim eq_refl: forall x. eq(x, x)
```

- Contains `include` directives, `axiom` statements (with optional `@def`), and `claim` statements
- No `proof` blocks
- Includes use `#pragma once` semantics: loading the same file twice silently skips it
- Include graph must be acyclic

### .fol.proof (Proof files)
```fol
proof eq_refl:
    fix x
    ext = use extensionality
    # ... proof steps ...
    qed h8
```

- Contains only `proof` blocks (and comments)
- No `axiom`, `claim`, or `include` directives
- Each proof block proves one claim from the corresponding `.fol.def` file
- Proofs can `use` axioms and previously proven theorems

## Bazel Proof Rules

Defined in `build/fol.bzl`, and `build/fol_unit.bzl` for the translated unit.

### `fol_library` — Header-only target (axioms + claims)
```python
fol_library(
    name = "nat_lib",
    header = "nat.fol.def",
    deps = ["@zf//:ZF.Nat"],
)
```

### `fol_proof` — Proof verification target
```python
fol_proof(
    name = "nat",
    header = "nat.fol.def",
    proof = "nat.fol.proof",
    deps = ["@zf//:ZF.Nat"],      # fol_library, fol_proof or fol_group deps
)
```

- Runs `proof_checker` to verify all claims in the header are proved
- Only checks claims **new** to the header (not inherited from deps)
- Produces a `.proven` marker file on success, and a `.report` with the status of every claim and schema
- Also acts as a `FolInfo` provider, so other `fol_proof` targets can depend on it

### `fol_group` — Several targets as one dep
```python
fol_group(
    name = "base",
    deps = [":axioms", ":pairs"],
)
```

### `fol_unit` — A translated unit as a repository
Declared in `MODULE.bazel`. It checks the unit against `lib/zf.sha256` and generates one `fol_proof` per part, citing the parts its line in the unit's `parts` file names, and `@zf//:parts`, a `fol_group` of them all. `FOL_UNIT` names a unit elsewhere than `~/isa2fol-units`.

### Dependency chain
```
//lib:base (fol_group) — the 19 axioms and 13 tiers
  └── @zf//:Pure, :IFOL, :FOL, :ZF.* (fol_proof) — the translated parts
        └── //math:nat (fol_proof)
```

### proof_checker binary

`src/tools/proof_checker.cpp` — standalone binary used by `fol_proof`:
```
Usage: proof_checker [--lib out.fol.lib] <header.fol.def> <proof.fol.proof> [dep1.fol.def|dep1.fol.lib ...]
```
1. Loads dependencies (libraries from the Bazel depset, deps first)
2. Loads the main header
3. Loads and executes the proof file, one block at a time
4. Verifies all new claims (not from deps) are proved
5. With `--lib`, writes what the header and its proofs add as a library
6. Writes a `.proven` marker file via `FOL_OUTPUT` env var

## Build Dependencies

```
src/core:formula     <- //src/util:registry, //src/util:error
src/parser           <- //src/core:formula
src/runtime          <- //src/core:formula, //src/parser
src/tools:proof_checker <- //src/runtime
test:core_test       <- //src/core:formula, //src/parser
test:runtime_test    <- //src/runtime, //src/parser
```

## Proof Syntax

Proofs can be written in a declarative syntax and executed by the runtime.

### Syntax

```fol
# Axioms and claims (must be sentences - no free variables)
axiom all_P: forall x. P(x)
@def(P) axiom p_def: forall x. (P(x) <-> Q(x))   # Definition axiom
axiom all_P_impl_Q: forall x. (P(x) -> Q(x))
claim all_Q: forall x. Q(x)

# Proof block
proof all_Q:
    fix x                           # Introduce eigenvariable
    h1 = use all_P                  # Use axiom
    h2 = forall_elim h1, x          # Instantiate with fixed var
    h3 = use all_P_impl_Q
    h4 = forall_elim h3, x
    h5 = implies_elim h4, h2        # Modus ponens
    h6 = forall_intro h5            # Generalize
    qed h6
```

### Important: Sentences Only

**Axioms and claims must be sentences (formulas with no free variables).**

- ✓ `forall x. P(x)` - valid sentence (x is bound)
- ✓ `forall x. (P(x) -> Q(x))` - valid sentence (x is bound)
- ✗ `P(x)` - invalid (x is free)
- ✗ `P(a)` - invalid (a is free, not a constant)

If you want to assert something about a variable, quantify it:
- Instead of `axiom P_x: P(x)` (invalid)
- Use `axiom all_P: forall x. P(x)` (valid)

### Available Rules

```
# Statement types
axiom name: <formula>                # Axiom (assumed true)
@def(P) axiom name: <formula>       # Definition axiom for predicate P (prevents redefining P)
claim name: <formula>                # Claim (must be proved)

# Scope management
fix x                   # Introduce eigenvariable x
h = assume <formula>    # Assume formula (can reference fixed vars)
h = let <formula>       # Create formula handle without assuming (for or_intro)
h = use <name>          # Use axiom or theorem by name

# Conjunction
and_intro h1, h2        # A, B ⊢ A ∧ B
and_elim_l h            # A ∧ B ⊢ A
and_elim_r h            # A ∧ B ⊢ B

# Disjunction
or_intro_l h1, h2       # A, B_formula ⊢ A ∨ B (h1 derived, h2 just formula)
or_intro_r h1, h2       # A_formula, B ⊢ A ∨ B (h1 just formula, h2 derived)
or_elim h_or, h_ac, h_bc # A ∨ B, A→C, B→C ⊢ C

# Implication
implies_intro h         # [A] ⊢ B closes scope → A → B
implies_elim h_impl, h  # A → B, A ⊢ B

# Negation
not_intro h_bot         # [A] ⊢ ⊥ closes scope → ¬A
not_elim h_neg, h       # ¬A, A ⊢ ⊥

# Biconditional
iff_intro h_ab, h_ba    # A→B, B→A ⊢ A ↔ B
iff_elim_l h_iff, h_a   # A ↔ B, A ⊢ B
iff_elim_r h_iff, h_b   # A ↔ B, B ⊢ A

# Quantifiers
forall_intro h          # [x] ⊢ P(x) closes fix scope → ∀x.P(x)
forall_elim h, term     # ∀x.P(x), t ⊢ P(t)
exists_intro h          # P(t) ⊢ ∃x.P(x) (or closes exists scope)
exists_intro h, t       # P(t) ⊢ ∃x.P(x) (with explicit witness term)
exists_elim h           # ∃x.P(x) ⊢ opens witness scope
exists_elim h, name     # same, but names the witness for use in forall_elim

# Equality
eq_sym h_eq             # eq(a,b) ⊢ eq(b,a)

# Classical
double_neg_elim h       # ¬¬A ⊢ A
excluded_middle h       # ⊢ A ∨ ¬A

# Definite descriptions (Hilbert ε)
iota_elim h             # ∃x.φ(x) ⊢ φ(ιx.φ(x))
iota_elim h, t          # same, but names the iota term t for use in forall_elim
```

### Substituting Equals

There is no built-in substitution rule. Equality is axiomatized by `extensionality` and `elem_first_subst` in `lib/base/axioms.fol.def`, and substitution goes through lemmas:

- `elem_first_subst`: `eq(x, y) -> (elem(x, s) -> elem(y, s))` (element position)
- `elem_second`: `eq(s, t) -> (elem(x, s) -> elem(x, t))` (set position)
- `cong_elem_l`, `cong_elem_r`: the same as biconditionals (`lib/base/tiers/cong.fol.def`)
- `set_cong`: `eq(x, y) -> (set(x) -> set(y))`
- For a defined predicate, unfold its `@def` axiom, substitute inside, and fold back.

```fol
# Example: from eq(x,y) and elem(x,s), derive elem(y,s)
h_eq = ...          # eq(x, y) - derived
h_elem = ...        # elem(x, s) - derived
ee = use elem_first_subst
ee1 = forall_elim ee, x
ee2 = forall_elim ee1, y
ee3 = forall_elim ee2, s
ee4 = implies_elim ee3, h_eq
h_result = implies_elim ee4, h_elem   # elem(y, s)
```

## Writing Tests

### Critical Rule: Sentences Only

**All axioms and claims in tests MUST be sentences (no free variables).** This is the most common mistake.

```cpp
// WRONG - free variable 'a'
rt.load("axiom P_a: P(a)");

// CORRECT - all variables bound
rt.load("axiom all_P: forall x. P(x)");
```

### Standard Test Pattern

When testing proofs, use the fix/forall_elim/forall_intro pattern:

```cpp
bool test_example() {
    Runtime rt;

    // All axioms and claims must be sentences
    rt.load(R"(
        axiom all_P: forall x. P(x)
        axiom all_P_impl_Q: forall x. (P(x) -> Q(x))
        claim all_Q: forall x. Q(x)
    )");

    auto ctx = rt.prove("all_Q");

    // 1. Fix a variable (creates eigenvariable)
    Term x = ctx.fix_var();

    // 2. Use axioms and instantiate with fixed var
    auto all_p = ctx.use("all_P");
    auto p_x = ctx.forall_elim(all_p.value(), x);

    auto all_pq = ctx.use("all_P_impl_Q");
    auto pq_x = ctx.forall_elim(all_pq.value(), x);

    // 3. Apply rules
    auto q_x = ctx.implies_elim(pq_x.value(), p_x.value());

    // 4. Generalize back to forall
    auto all_q = ctx.forall_intro(q_x.value());

    // 5. Complete proof
    auto result = ctx.qed(all_q.value());
    return result.ok();
}
```

### Proof Syntax Tests

For testing the declarative proof syntax:

```cpp
bool test_proof_syntax() {
    Runtime rt;

    auto result = rt.load_with_proofs(R"(
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
    )");

    if (!result.ok()) return false;

    auto exec = rt.execute_all_proofs(result.value());
    return exec.ok();
}
```

### Testing with assume and let

The `assume` and `let` keywords can reference fixed variables by name:

```cpp
bool test_assume_with_fixed_vars() {
    Runtime rt;

    auto result = rt.load_with_proofs(R"(
        axiom pair_def: forall p. forall a. forall b. (pair(p, a, b) <-> ...)
        claim pair_elems: forall p. forall a. forall b. forall z.
            ((pair(p, a, b) & elem(z, p)) -> ...)

        proof pair_elems:
            fix p
            fix a
            fix b
            fix z
            h = assume pair(p, a, b) & elem(z, p)   # References fixed vars
            h_pair = and_elim_l h
            # ... rest of proof
            qed result
    )");

    return result.ok() && rt.execute_all_proofs(result.value()).ok();
}
```

### Common Mistakes to Avoid

1. **Using constants**: There are no constants. `P(a)` treats `a` as a free variable.
   ```cpp
   // WRONG
   rt.load("axiom foo: P(a) -> Q(a)");

   // CORRECT
   rt.load("axiom foo: forall x. (P(x) -> Q(x))");
   ```

2. **Forgetting forall_intro**: After working with a fixed variable, generalize back.
   ```cpp
   Term x = ctx.fix_var();
   // ... derive Q(x) ...
   auto all_q = ctx.forall_intro(q_x);  // Don't forget this!
   ```

3. **Using Term::constant()**: This no longer exists. Use only fixed variables from `fix_var()`.

4. **Using assume/let before fix**: Variables must be fixed before they can be used in assume or let.
   ```fol
   # WRONG - x not fixed yet
   h = assume P(x)
   fix x

   # CORRECT - fix first, then assume
   fix x
   h = assume P(x)
   ```

## Example: Ordered Pair Proofs

The `test/corpus/basics/ordered_pair.fol.def` and `test/corpus/basics/ordered_pair.fol.proof` files contain proofs about Kuratowski ordered pairs:

```fol
# Definition: (a, b) = {{a}, {a, b}}
@def(pair) axiom pair_def: forall p. forall a. forall b. (pair(p, a, b) <->
    forall z. (elem(z, p) <->
        (forall w. (elem(w, z) <-> eq(w, a))) |
        (forall w. (elem(w, z) <-> (eq(w, a) | eq(w, b))))))

# Prove: singleton {a} is in pair (a, b)
proof singleton_in_pair:
    fix p
    fix a
    fix b
    fix s
    h = assume pair(p, a, b) & singleton(s, a)
    h_pair = and_elim_l h
    h_sing = and_elim_r h
    # Expand pair_def
    pdef = use pair_def
    pdef1 = forall_elim pdef, p
    pdef2 = forall_elim pdef1, a
    pdef3 = forall_elim pdef2, b
    h_all_z = iff_elim_l pdef3, h_pair
    h_s_iff = forall_elim h_all_z, s
    # Expand singleton_def to get D1
    sdef = use singleton_def
    sdef1 = forall_elim sdef, s
    sdef2 = forall_elim sdef1, a
    h_d1 = iff_elim_l sdef2, h_sing
    # Use let to create D2 formula for or_intro
    d2 = let forall w. (elem(w, s) <-> (eq(w, a) | eq(w, b)))
    h_disj = or_intro_l h_d1, d2
    elem_s_p = iff_elim_r h_s_iff, h_disj
    h_impl = implies_intro elem_s_p
    h4 = forall_intro h_impl
    h3 = forall_intro h4
    h2 = forall_intro h3
    h1 = forall_intro h2
    qed h1
```

Key techniques demonstrated:
- **fix**: Introduce eigenvariables for universal quantifier proofs
- **assume**: Assume antecedent for implication introduction
- **let**: Create formula handles for `or_intro` without assuming them
- **forall_elim**: Instantiate universal axioms with fixed variables
- **iff_elim_l/r**: Extract directions from biconditionals
- **forall_intro**: Generalize over fixed variables

## Design Decisions

1. **De Bruijn indices**: Variables are indices, not names. Simplifies substitution.

2. **Formula interning**: All formulas stored in ProofDatabase. Equality by ID comparison.

3. **Theory vs ProofDatabase**: Theory holds global axioms/theorems. ProofDatabase is the formula arena shared across all proofs in a theory.

4. **Pre-generated parser**: Flex/Bison outputs committed to repo for clangd compatibility.

5. **RAII scopes**: `AssumptionScope` and `EigenvariableScope` ensure proof soundness automatically.

6. **Sentences only**: Axioms and claims must be sentences (closed formulas with no free variables). This ensures soundness.

7. **No constants**: The system only has variables (generalized and fixed). All terms in axioms/claims must be bound by quantifiers.

8. **Deferred formula parsing**: Formulas in `assume` and `let` proof steps are parsed during proof execution, not at file parse time. This allows them to reference fixed variables by name.

9. **Header/proof split**: `.fol.def` files contain axioms and claims, `.fol.proof` files contain proofs. This enables incremental Bazel-based verification and separates interface from implementation.

10. **#pragma once includes**: `load_file_recursive` silently skips already-loaded files (by canonical path). Diamond dependencies (A includes B and C, both include D) work correctly.

11. **`@def` annotations**: `@def(P) axiom name: φ` marks an axiom as the definition of predicate `P`. The predicate must appear in the formula, and redefining the same predicate with a different axiom is a parse error. Re-registration of the same predicate+axiom pair is idempotent (for `#pragma once` compatibility). At the core level, `@def` axioms are still axioms. `GlobalContext` tracks `defined_predicates_` as a map from predicate name to axiom name.
