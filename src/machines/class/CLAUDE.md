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

## 4. Production designs are the user's, decided after a test

The machine is part of a commercial product, with sys2fol. A production design is one a client relies on, or one other
work is built on and costly to change: the claims' shapes, any name a person writes or reads, the request, the
interface, and what is trusted.
For each:

1. Explain it: the problem, the options, their trade-offs and a recommendation.
2. Check the user followed it: two or three questions on the explanation itself (what the choice commits to, why the
   recommendation, what it costs and leaves open), asking only what making the choice needs, never an exercise. Check the
   answers and explain what an answer misses; ask again only when the gap bears on the choice, never the same question
   twice. The explanation's weight is on the trade-offs.
3. The user decides, and the decision goes into `DESIGN.md` as theirs.

Never decide one, never build on one not yet decided, and never take agreement with a recommendation for a passed test.
Any other design is written into `DESIGN.md` and agreed before it is built.

## 5. C++

The machine is C++ (Bazel), run under a memory cap.
