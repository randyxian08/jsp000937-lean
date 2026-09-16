# JSP-000937 statement correspondence

Original problem: https://www.erdosproblems.com/1130

| Requirement | Formal representation |
| --- | --- |
| n distinct real interpolation nodes in [-1,1] | `Erdos1153.NodeFamily n`: `Fin n → ℝ`, injectivity and interval membership. |
| Literal Lagrange cardinal functions | `lagrangeFundamental` in `Erdos1153/Statement.lean`, product over every other original node. |
| Lebesgue function | `lebesgueFunction`, sum of the absolute cardinal values. |
| All n+1 intervals | `augmentedGapHeight` includes `[-1,x_first]`, `[x_last,1]` and every internal adjacent gap. Exterior endpoints are interval boundaries, not additional interpolation nodes. |
| Minimum of interval maxima | `allMinPeak := sInf (Set.range (augmentedGapHeight nodes))`; finite nonempty range. Interval maxima are attained by continuity and compactness. |
| Arbitrary enumeration and free endpoints | Competitors are `NodeFamily (d+2)` and sorted internally; no fixed-endpoint or ordering assumptions are placed on them. |
| Maximizer existence and classification | `Target937Classification`, proved by `jsp_000937_classification`, including a separate one-node case. |
| Uniform logarithmic bound | `Target937Logarithmic`: `∃ C > 0, ∀ d, ∀ nodes : NodeFamily (d+2), allMinPeak nodes ≤ C * log (d+2)`. C is chosen before cardinality and nodes. |
| Both requests together | `Target937 := Target937Classification ∧ Target937Logarithmic`, proved by `jsp_000937`. |
| Explicit constant | `logConstant = 4 + (π+5)/log 2`; positivity proved. The n=1 case is excluded from the logarithmic estimate, not from classification. |
| Strict variant | `allMinPeak_lt_explicit_log` uses the constant `logConstant+1`. |
| Executable target check | `Audit937.lean` checks both independent targets and prints their axiom dependencies. `AuditFull.lean` checks compatibility with the other results. |

The upper-bound chain uses the comparison `U(X) ≤ Λ(Z)` for every competitor Z.
`chebyshevNodes` constructs n distinct nodes `cos((j+1/2)π/n)`.
`CardinalIdentity` derives the cardinal formula from polynomial factorization
and exact interpolation. `TrigonometricBounds` controls angular denominators;
`HarmonicPacking` bounds the sum by `π+1+4H_n`; the Mathlib harmonic estimate
and `n≥2` give a uniform multiple of `log n`.

The maximizer classification imposes **lower bounds**, not equality, on the
two exterior peaks of positive affine copies of the internally equioscillating
reference. It does not assert that all n+1 peaks are equal, nor uniqueness of
unrestricted maximizers. Informal historical summaries suggesting those
stronger claims should be reviewed against the literal objective and original
sources; they are not silently encoded as the target.

The independent `Definitions.lean` is byte-for-byte unchanged from the earlier
candidate (SHA-256 `985db07ef4429ddd2f83bf2f44952de09965f81799e7f8271267c5bb8b06d9cc`).
The submitted compiler repairs change proof terms, not target quantifiers or
hypotheses. No added project axioms, proof placeholders, or raised heartbeat
limits are used. Kernel correctness and correspondence to the prize entry
remain distinct review questions.
