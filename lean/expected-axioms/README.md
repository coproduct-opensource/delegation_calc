# Expected axioms snapshot

Each `<theorem>.txt` file is the expected output of `#print axioms <theorem>`
on the named theorem. CI compares actual `#print axioms` against these
snapshots and fails on any difference. This catches the case where a new
axiom is introduced silently (a soundness regression in disguise).

Lean's foundational axioms are always present and acceptable:

  propext, Classical.choice, Quot.sound

Any other axiom in the snapshot is *intentional* and must be justified in
the relevant theorem's docstring.

To regenerate after an intentional change:
```bash
cd lean
lake env lean --run scripts/print_theorem_axioms.lean <theorem> > expected-axioms/<theorem>.txt
```
