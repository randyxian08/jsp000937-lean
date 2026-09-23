# JSP-000937: all-gap interpolation maximin and logarithmic bound

Submitted by [randyxian08](https://github.com/randyxian08).

This repository contains a checked Lean 4 proof of the full real-interval
statement used for [Erdős problem 1130](https://www.erdosproblems.com/1130),
catalogued as [JSP-000937](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000937).

For distinct interpolation nodes in `[-1,1]`, the objective is the minimum
of the maxima of the Lebesgue function over **all n+1 intervals**, including
both exterior intervals. The theorem proves:

1. Existence and classification of every maximizing node configuration,
   including the one-node case, without fixing competitors' endpoints.
2. A single uniform `C log n` upper bound for every `n ≥ 2` and every node
   configuration, with `C = 4 + (π + 5) / log 2 > 0`.

The final declaration is `JSPFreeNodes.jsp_000937 : JSPFreeNodes.Target937`,
where `Target937 = Target937Classification ∧ Target937Logarithmic`.
This includes both parts, rather than only the previously checked classification.

## Sources and statement

- [Independent definitions and targets](Erdos1153/JSPInterpolation/Definitions.lean).
- [Final theorem and explicit upper bounds](Erdos1153/JSPInterpolation/Logarithmic.lean).
- [All-gap maximizer classification](Erdos1153/JSPInterpolation/AllGaps.lean).
- [Chebyshev competitor and global bound](Erdos1153/JSPInterpolation/Logarithmic/Chebyshev.lean).
- [Statement correspondence](STATEMENT-CORRESPONDENCE.md).
- [Provenance and public authorship attestation](PROVENANCE.md).

The classification describes positive affine copies of a canonical
internally equioscillating reference, with both exterior endpoint peaks at
least the reference height. The normalized reference itself is not claimed
to maximize the all-gap objective. All-gap equioscillation or uniqueness of
unrestricted maximizing configurations is not asserted.

The logarithmic proof constructs actual Chebyshev root nodes and proves
`U(X) ≤ Λ(Z) ≤ π + 1 + 4 H_n ≤ π + 5 + 4 log n ≤ C log n`.
The constant is not claimed to be sharp.

## Reproduce

Install elan, Git and Python 3, then run:

```sh
bash verify.sh
```

Lean is pinned to 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, with exact dependencies in
`lake-manifest.json`. The script builds the library and final target modules,
checks the full target, prints actual axiom reports, checks the allowlist,
replays the final module with `leanchecker`, and scans project sources.

The earlier 4.27.0 verification log remains in
[evidence/local-verification.log](evidence/local-verification.log) as historical
evidence; it does not establish verification of this upgraded snapshot.
The upgraded snapshot has a separate [Lean 4.33.0 local verification record](evidence/lean433-local-verification.md).
The final axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Local verification uses macOS arm64 and previously built dependencies;
it is not an independent human review or an independent kernel implementation
check. Consult GitHub Actions for the actual Linux reproduction status.

Related submissions #129 and #96 in the prize repository concern JSP-000936
and JSP-000958. Their theorems remain included as supporting library results;
this submission requests consideration for JSP-000937 only.

Passing Lean checks does not establish first-formalization priority, recipient
confirmation, award eligibility or payment. Those remain for organizer review.
