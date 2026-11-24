# The compression machine

A proof file in, a smaller one out, which `proof_checker` checks like any other. The machine is untrusted and adds
nothing to the checker or the logic: every block it rewrites is run by the checker's own `execute_proof` before it is
kept, and the output is checked again by `proof_checker`.

## 1. What it removes

The checker holds a fact as its formula and the scopes it rests on (`src/proof/nd/stack.cpp`, `derive_with_deps`). A
step deriving a formula already held on scopes no deeper changes nothing, and a rule reads a cited step only through
its formula. The machine replays each block on the checker's own proof stack, over the formulas
`NDVerifier::trace_full` gives, and records for every held fact the step that set its entry. It keeps:

- the qed;
- for each held fact a kept step reads, the step that set the fact's entry, which the citation now names;
- for each formula read bare (`or_intro`'s other side, `bottom_elim`'s target, `excluded_middle`'s and `peirce`'s
  formulas), the step holding it if one does, else the step cited;
- the steps binding the terms and the names a kept step reads;
- the opener and the closer of every scope holding a kept step.

Everything else goes: a step nothing kept reads, and every re-derivation, which is never the step a fact is read from.
A fact proved in a scope it does not depend on stays held after the scope closes, so a later scope reads it from there.

## 2. What it writes

- A step's name is reused once the step it named is read no more; the most-read steps take the shortest names.
- A term a step binds (`fix x`, `exists_elim h, x`, `iota_elim h, x`) is renamed `_a`, `_b`, …, the most-read first,
  and a bound variable is named by its depth. The checker reads neither name: a bound variable is its position, a
  fixed one the step that binds it. Names starting with `_` are never a step's, since lowering binds a `fix`'s name as
  a step name too.
- Formulas carry the parentheses the grammar needs and no space it does not.

## 3. The gate

Each rewritten block is parsed back and run by `Runtime::execute_proof`, as `proof_checker` runs it, and kept only if
it checks. Otherwise the block is written as given, reprinted with its own names. A block failing as given is
registered unproved, as `proof_checker` registers it, so that the blocks citing it still lower. A block that checks as
given but not reprinted is an error.

## 4. Interface

- **Library:** `//src/machines/compress`, `compress(Runtime&, FILE*, std::ostream&, Stats&)`. The runtime holds the
  dependencies and the header, and gains each block's claim as `proof_checker` registers it.
- **Command line:** `fol_compress OUT HEADER PROOF DEP... [-- DEP_PROOF...]`, loading as `proof_checker` does.
- **Bazel (`defs.bzl`):** `fol_compress` writes the compressed file; `fol_compressed_proof` is it with the `fol_proof`
  that checks it.
- The class machine's command line compresses its proof in process, over the libraries it has loaded. sys2fol's
  proofs from sysprove go through `fol_compressed_proof`.

## 5. Cost

Every block of these outputs is rewritten and every report is Proved:

| Proofs | Lines in → out | Bytes in → out |
|---|---|---|
| Class machine, sys2fol's 13 requests | 12,168 → 12,063 | 669 KB → 379 KB |
| Class machine, its 17 rows | 15,753 → 15,542 | 589 KB → 321 KB |
| sysprove, BoundedQueue's claims | 5,687 → 5,126 | 366 KB → 161 KB |
| sysprove, BoundedQueue's lemmas | 4,998 → 4,867 | 206 KB → 103 KB |
| sysprove, Crossing's claims | 4,343 → 3,094 | 228 KB → 79 KB |
| sysprove, Crossing's lemmas | 3,185 → 2,728 | 130 KB → 57 KB |
| `math/systems`, hand-written and machine-made | 20,143 → 18,541 | 777 KB → 394 KB |

A pass costs about one check: it loads the libraries as `proof_checker` does, and its replays take less.

## 6. Not done here

Moving a step out of a scope it does not depend on, so that a scope kept only for it could go; closing a repeated
sub-derivation once over the names it differs in; and what a writer's structure decides (schemas, rows, bodies proved
in place), which only the writer can change.

## 7. Decided by the user

| # | Decision | Reason |
|---|---|---|
| 1 | The machine lives in fol-zfc-comb-lib's `src/machines/compress`, beside the class machine, built on the checker's public replay (`NDVerifier::trace_full`, the proof stack), and it follows the checker's proof format when that changes (the user, 2026-11-24) | Every producer of fol-zfc proofs reaches it, the class machine included, which sys2fol or a repository of its own would not allow; the checker's tree stays as it is. |
