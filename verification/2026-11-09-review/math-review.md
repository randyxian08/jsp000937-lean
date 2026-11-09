# Mathematical correspondence review: JSP-000937 / Erdős 1130

Selected proof: `c6819617f4d8de6afcbf63da31544ce2902f7b6a`, `randyxian08/jsp000937-lean`. Review date: 2026-11-09. AI-assisted submitter-side review; not an independent mathematician's report or official decision.

## Source and exact task

The main question at <https://www.erdosproblems.com/1130> concerns distinct real interpolation nodes in [-1,1], the sum of absolute values of their Lagrange fundamental polynomials, and the minimum of the maxima on all n+1 intervals, including the two exterior intervals. It asks for a uniform logarithmic upper bound and a description of maximizing nodes. The direct problem page could not be retrieved during this run; the same site's indexed discussion page exposed the main statement. The original 1978 paper was downloaded from author Allan Pinkus's university site: <https://pinkus.net.technion.ac.il/files/2021/02/conj.pdf> (J. Approximation Theory 24, pp. 289–303).

The paper fixes the extreme interpolation nodes to a,b and considers **internal** gap peaks (pp. 289–290). Its Theorem 1 gives the unique equioscillating reference, and Theorem 2 (p. 298) gives coordinatewise gap-height rigidity. These are ingredients for this submission's free-node derivation, not by themselves an identification of the original all-gap objective with an internal-gap objective.

## Definition and quantifier checks

- `NodeFamily n` consists of an injective function `Fin n → ℝ` with every value in [-1,1]. No competitor endpoint, ordering, separation, or equioscillation assumption is present. Sorting identifies the consecutive intervals and preserves the original function.
- `lagrangeFundamental` is the literal product of normalized linear factors. The denominator cannot vanish for an erased, distinct index. The Lebesgue function is the sum of their absolute values.
- `lebesgueOn` is a supremum on a closed interval. Continuity and compactness prove that this is an attained maximum on all nonempty intervals used here, including degenerate exterior intervals.
- `allMinPeak` takes the infimum over a finite nonempty range with exactly two exterior peaks and n−1 internal peaks. Neither boundary is inserted as an extra interpolation node.
- The reference configuration, not an arbitrary competitor, has normalized endpoints and equal internal peaks. The logarithmic constant is existentially chosen before the cardinality and node family.
- The final theorem is a conjunction of classification and logarithmic growth. The one-node case is separately classified; a C log(1) estimate would be false and is not asserted. All n≥2 are represented by d+2, including d=0.

## Mathematical chain

The source de Boor–Pinkus comparison theorem is proved in the base development, not a custom axiom. Affine transport places any competitor's actual extreme-node interval into the reference framework. The strict comparison/rigidity consequence bounds its internal minimum by the reference height h and characterizes equality as an affine copy of the reference.

The actual all-gap minimum is exactly `min(left exterior peak, internal minimum, right exterior peak)`. On either exterior interval the maximum is at the ambient endpoint. Thus equality to h holds exactly for an admissible positive affine reference copy with both endpoint values at least h. Attainment is proved by compressing the reference by a=1/(|h|+2). Exact interpolation of p(x)=x gives `|x| ≤ a L(x)` at the ambient endpoints, so both exterior peaks exceed h. This supplies a real maximizer, rather than assuming one or using the endpoint-fixed reference as a false witness.

For the logarithmic bound, the all-gap optimum is no larger than the global Lebesgue constant of any competing array. The proof constructs actual Chebyshev root nodes, derives their cardinal identities from polynomial interpolation, treats exact-node hits before dividing, and chooses the angularly nearest root. The nearest term is bounded by π+1; other terms are bounded by 2 divided by their integer index distance. Summing both sides gives π+1+4H_n. The harmonic estimate then yields the single explicit constant `C = 4+(π+5)/log 2`. It is positive and independent of the original nodes and n≥2. No sharp leading coefficient is claimed or needed for the main O(log n) request.

## Necessary distinction from background wording

The webpage's background says maximizing configurations are characterized by **all** n+1 peaks being equal. Read literally with unrestricted nodes, that necessity already fails for two nodes: nodes −1/2,+1/2 have exterior peaks 2,2 and internal peak 1, yet their minimum is the optimal value 1. Every two-node configuration has internal Lebesgue function identically 1 and all peak heights at least 1. This exact calculation is recorded separately. For n≥3, a normalized endpoint-fixed reference has all-gap value 1 and need not maximize; the source includes a formal regression theorem establishing this distinction.

The submitted target solves the literal main optimization problem with a shape-plus-exterior-tests classification; it does **not** prove that inaccurate all-gap equioscillation equivalence. This discrepancy must be explicit in a reviewer-facing scope judgment. The final classification is implicit via the unique canonical reference, as in the cited paper; it is not a closed formula for each individual optimal node.

## Authorship and verification limits

The base development is attributed in the source to Ethan Yang / ethn-y at `03bd3e064c0b95e8e7d335fa0f3e3de0713ca777`. Its existing same-person attestation linking that name to randyxian08 was not verified in this audit. No identity or ownership inference is made from a successful build, and no new identity attestation is published. The additions under `JSPInterpolation` and their inherited proof dependencies must be credited separately. The present mathematical review found no blocking error in the stated chain; actual execution and axiom results are recorded separately and do not establish priority or an award.
