# Gibbard–Satterthwaite theorem in Lean 4

Formalization of the Gibbard–Satterthwaite theorem: with three or more
alternatives, every onto strategy-proof social choice function is dictatorial.

## Proof strategy

The theorem is proved by reduction to Arrow's impossibility theorem. The
`Arrow/` modules are the verified Arrow formalization
(`arrow-impossibility-lean`, same author): core definitions, field expansion,
group contraction, and the main Arrow theorem with zero sorries and axioms
limited to `propext`, `Classical.choice`, `Quot.sound`.

`GS/Basic.lean` defines social choice functions, strategy-proofness, onto-ness,
and dictatorship. `GS/Reduction.lean` builds a social welfare function from a
strategy-proof onto SCF (via top-two profiles), shows it satisfies unanimity
and IIA, applies Arrow to obtain a dictator, and transfers dictatorship back
to the SCF.

`Challenge.lean` / `Solution.lean` package the Palomar registry submission;
see `comparator.json` and `formalization.yaml`.

Built with Lean 4 / Mathlib `v4.35.0-rc2`.
