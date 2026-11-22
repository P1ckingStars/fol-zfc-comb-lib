# Hard rules for Claude in the class machine

The repository's own rules (`/CLAUDE.md`) hold here. In addition:

## 1. Only checked proofs count

Every claim the machine writes is checked by `//src/tools:proof_checker`. Read its Proved list: the exit status and a
`.fol.lib`'s status can report a false claim as Proved.

## 2. A machine, never the checker

The machine writes plain fol-zfc steps and is not trusted; a formula it cannot prove gets nothing (ai-fol `DECODER.md`
D22). Nothing here is linked into the checker, and nothing here adds a rule, a normalizer or a decision procedure to it
or to the logic.

## 3. Translate by the construction

Every input construct has one row of isa2fol `docs/FOUNDATION.md` §3 or is refused at the input gate.

## 4. Design before code

Write a design into `DESIGN.md` and get the user's agreement before building it. What a claim states is the user's
decision: propose, never decide.

## 5. C++

The machine is C++ (Bazel), run under a memory cap.
