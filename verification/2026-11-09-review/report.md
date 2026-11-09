# JSP-000937 / Erdős 1130: dated verification report

**Overall verdict: Verification passed for the literal main real-interval problem, within the standard classical Lean trust scope stated below.** At proof commit `c6819617f4d8de6afcbf63da31544ce2902f7b6a`, the checked formalization supplies both the all-gap maximizer classification and a uniform logarithmic upper bound. It does not prove the webpage background's stronger all-peaks-equal equivalence, which is false for unrestricted nodes already at n=2. This is an AI-assisted submitter-side review, not independent human review, organizer acceptance, identity approval, priority determination, or an award decision.

| Required question | Judgment | Decisive evidence |
| --- | --- | --- |
| Addresses the specified original problem? | Yes, the two literal main requests on the real interval. | Literal Lagrange/all-gap formula bridge, free-node domain and quantifier review; [mathematical review](math-review.md). |
| Did the specified commit actually pass? | Yes. | Unmodified clean build exit 0; 8 target checks, source re-elaboration, all axiom reports and final module replay exit 0. |
| Fully solves the original problem? | Yes for those main requests, including all positive-cardinality classification cases and the n≥2 logarithmic bound. | Both conjuncts of `Target937`; an actual maximizer, both directions of classification, all n+1 intervals. No sharp leading constant or false background equivalence is claimed. |
| Meets Lean completeness requirements for this review? | Meets at the actual Lean/source/axiom and same-kernel replay levels. | Only standard `propext`, `Classical.choice`, `Quot.sound`; no extra premises or proof gaps in the checked declarations. Higher independent verification and prize prerequisites are separately limited below. |

## Pinned record and original scope

- [Existing PR #765](https://github.com/TheJustinSunPrize/awards/pull/765), open at retrieval. Awards base `bcf1866ea9a4ae82b32bd95b82ffd812b9ee80d2`; head `ed78608840fd05b90d915e5bcdebef242a97614a`, branch `codex/rules-migration-jsp-000937`, `randyxian08/awards`. Its diff contains only two relevant catalog rows. All 3 commits, 2 discussion comments, 0 reviews and 0 inline comments were retrieved; no missing review is inferred from the visual webpage.
- [Proof A](https://github.com/randyxian08/jsp000937-lean/tree/c6819617f4d8de6afcbf63da31544ce2902f7b6a), project root at repository root, contained in the retrieved `main` tip `4d7493e7e730597877c38bd750bf02839863b68a`. That later tip adds only historical verification artifacts; the original Lean sources and toolchain/lockfiles are identical to A.
- [Original problem](https://www.erdosproblems.com/1130), cross-checked through the original site's indexed [discussion page](https://www.erdosproblems.com/forum/thread/1130). Direct retrieval failed; no claim about current website endorsement is based on that index.
- [de Boor–Pinkus 1978 paper, author-hosted copy](https://pinkus.net.technion.ac.il/files/2021/02/conj.pdf), pp. 289–290, 295 and 298: fixed-endpoint internal peaks, canonical reference, and coordinatewise rigidity. Download SHA-256 `fabe52d72dba142d43a2836f6e8c1b441fdfd7ba18b8037cb402d92da7536209`. The copyrighted paper itself is not republished with this supplement.
- Workflow: [official lean-verify at f8801a8](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/skills/lean-verify/SKILL.md). The executed helper is included as text, SHA-256 `72a3901eea331853dbd65a843cd0b7f7b5b0255240ce1006c2cab1a51ffbea95`. Its code is identical to the official helper except for one extra terminal blank line; the original Git blob is `af21b87ecfbce38e12bc26357bc50bd5735aa0eb`. Its 13 utility tests completed with 12 passed and the optional real-Lean fixture skipped; these utility tests are not proof verification. The actual proof checks are recorded separately.

## Coverage

Pinned code: [all-gap definitions](https://github.com/randyxian08/jsp000937-lean/blob/c6819617f4d8de6afcbf63da31544ce2902f7b6a/Erdos1153/JSPInterpolation/Definitions.lean#L97), [classification](https://github.com/randyxian08/jsp000937-lean/blob/c6819617f4d8de6afcbf63da31544ce2902f7b6a/Erdos1153/JSPInterpolation/AllGaps.lean#L244), [attainment](https://github.com/randyxian08/jsp000937-lean/blob/c6819617f4d8de6afcbf63da31544ce2902f7b6a/Erdos1153/JSPInterpolation/AllGaps.lean#L157), [uniform bound](https://github.com/randyxian08/jsp000937-lean/blob/c6819617f4d8de6afcbf63da31544ce2902f7b6a/Erdos1153/JSPInterpolation/Logarithmic.lean#L36), [final conjunction](https://github.com/randyxian08/jsp000937-lean/blob/c6819617f4d8de6afcbf63da31544ce2902f7b6a/Erdos1153/JSPInterpolation/Logarithmic.lean#L67).

| Original obligation | Pinned proof / additional check | Assessment |
| --- | --- | --- |
| Distinct nodes anywhere in [-1,1], all n+1 interval maxima | `NodeFamily`, `augmentedGapHeight`, `allMinPeak`; `Review937.objective_eq` | Covered. Endpoints are boundaries, not added interpolation nodes. |
| Every maximizing configuration, both directions and existence | `jsp_000937_classification`, `raw_global_maximizer_iff` | Covered by positive affine reference copies and two exterior lower tests, with actual compressed witness. |
| A single positive C, uniform in n≥2 and in the node family | `jsp_000937_logarithmic`, `logarithmic_raw` | Covered by explicit `4+(π+5)/log 2`. |
| One-node classification / two-node boundary | `jsp_000937_one_node`, full d=0 target; exact boundary calculation | Covered. No false C log(1) estimate is asserted. |
| Both requests together | `jsp_000937 : Target937` | Covered, not a classification-only alias. |

The [independently written formula specification](audit/Specification.lean.txt) imports only Mathlib. Its Lagrange product and supremum/finite-minimum objective are related to the actual submission by [checked additional bridges](audit/Review937.lean.txt), including a raw increasing-coordinate logarithmic theorem and equivalence of ordered and unrestricted maximization. These files are audit harnesses, not an organizer-approved benchmark challenge. For unordered enumerations the original proof sorts without changing the interpolant.

The formula bridge represents n+1 intervals as a minimum of two exterior peaks and a finite minimum of n−1 internal peaks. All intervals are nonempty; continuity supplies attained maxima. The [mathematical review](math-review.md) explains the comparison argument, compression/attainment, actual Chebyshev competitor, exact-node cases and harmonic summation. It also explains why the two-node example does not invalidate this submitted classification, but does invalidate an overly strong informal summary.

## Environment and execution

Linux aarch64 / Debian 13.7, kernel 6.8.0-117-generic. Unprivileged uid/gid 10001, 3 CPU limit, configured 6 GiB container memory (VM effective memory observed about 3.813 GiB), pid limit 512, no-new-privileges. Only this audit's source/output and read-only trusted toolchain/helper were mounted; no host credentials, home or Docker socket. Networking was used to retrieve pinned dependencies, then disconnected before submitted-source compilation and checks.

Base image ID: `sha256:3a308cfa1f333c7dba5bf75020deb3e60c3429e9fcbc8b8a6dbd495b545499e4`. The base Dockerfile is supplied for reconstruction; a future package installation is not claimed to recreate that image bit for bit. The official Lean 4.33.0 Linux ARM archive SHA-256 was `f961a417cba10b6ea0a9d136712d5952813817ffd6680041f09a233526f803a9`, downloaded over HTTPS and mounted read-only after extraction. Compiler commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, Lake `5.0.0-src+d8b1897`; actual binaries `/opt/lean/bin/lean` and `/opt/lean/bin/lake`. No global user toolchain was changed.

All 9 package checkout revisions match the original manifest, including Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Mathlib's matching official precompiled cache was used (8690 entries); this is a clean build of custom proof source, not a recompilation of every standard-library/Mathlib dependency. One missing dependency target was compiled locally. Original proof `.olean` files were not accepted from the submitter.

| Step / cwd | Actual command and result | Evidence |
| --- | --- | --- |
| Prepare dependencies, `/project`, network enabled | `lake exe cache get`, exit 0 | [preparation log](logs/dependency-prepare.log), [9 revision checks](evidence/dependency-shas.json) |
| Unmodified source, `/project`, network disconnected | `lake build`, exit 0, 3066 jobs | [clean build](logs/unmodified-build.log) |
| Additional harness build | `lake build +Erdos1153.Review937`, final exit 0 | [check log](logs/additional-checks.log) |
| Support import used only by `AuditFull.lean` | `lake build +Erdos1153.JSPInterpolation.JSP958`, exit 0 | [support build](logs/support-module-build.log) |
| Official helper, `/project` | `python3 /tool/scripts/audit.py preflight /audit/targets.json --out /audit/preflight-01`; then `run ... --out /audit/check-01 --lake /opt/lean/bin/lake --timeout 300`, both exit 0 | [manifest](audit/targets.json), [preflight](audit/preflight-01/result.json), [8-target result](audit/check-01/result.json) |
| Source and axiom audits | `lake env lean Audit937.lean`; `lake env lean AuditFull.lean`; `python3 tools/check_axioms.py /logs/audit-full.log`, all exit 0 | [937 log](logs/audit937.log), [full audit](logs/audit-full.log) |
| Initial same-kernel replay | `lake env leanchecker Erdos1153.JSPInterpolation.Logarithmic`, exit 137 / OOM kill | [initial log](logs/leanchecker-oom.log), [resource evidence](evidence/kernel-resource-events.txt) |
| Low-memory replay retry | `LEAN_NUM_THREADS=1 lake env leanchecker -j1 Erdos1153.JSPInterpolation.Logarithmic`, exit 0 | [retry log](logs/leanchecker-retry.log). The pinned parser ignores `-j1`; the effective limit is the environment variable, per the official workaround. |

The helper explicitly rebuilt each named module, re-elaborated its exact source, and ran generated `#check`, `#print` and `#print axioms` files. Command arguments, exit codes and elapsed times are preserved in the machine result; target-result count is exactly 8, `mechanical_status=standard_axioms_only`, `inputs_stable=true`. The checked manifest intentionally leaves manual coverage pending; the semantic coverage table above records the separate completed assessment.

The initial orchestration reached and passed all target and original axiom audits, then exited 137 at its final default-parallel replay. Docker/cgroup confirmed one OOM kill. A justified retry limited worker parallelism with `LEAN_NUM_THREADS=1`, following the [Lean project's documented Mathlib-memory workaround](https://github.com/leanprover/lean-action/blob/main/README.md#run-leanchecker-on-a-project-with-a-mathlib-dependency), and passed. This is a resource/configuration retry, not a changed theorem or relaxed checker. The actual initial script is preserved; the low-memory reproduction variant is supplied separately. No initial all-stages exit-0 claim is made.

The first attempt at the new audit harness failed because an automated rewrite did not prove sorting invariance. The corrected harness supplies that equality explicitly. See [failure log](logs/harness-attempt-01.log) and [harness-only patch](audit/harness-repair.diff). No original proof source or statement was repaired. Temporary `sorryAx` output in that failed harness attempt is not a dependency of the successful final harness or original proof. Setup had an earlier Docker disk-capacity failure before proof checking; runtime/dependency storage was moved into this task's directory. A pre-build `leanchecker --help` probe also exited 1 because no project `.olean` existed; the final actual module replay above is the verification result. Deprecation/linter warnings remain and were not treated as proof errors.

## Actual target axioms

| Declaration | Mechanical status | Complete reported axiom list |
| --- | --- | --- |
| `JSPFreeNodes.jsp_000937` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |
| `JSPFreeNodes.jsp_000937_classification` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |
| `JSPFreeNodes.jsp_000937_logarithmic` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |
| `JSPFreeNodes.jsp_000937_one_node` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |
| `JSPFreeNodes.canonical_allMinPeak_eq_one` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |
| `Review937.objective_eq` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |
| `Review937.logarithmic_raw` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |
| `Review937.raw_global_maximizer_iff` | standard_axioms_only | `propext, Classical.choice, Quot.sound` |

The raw per-target logs retain all outputs. `Audit937.lean` checks the complete and logarithmic statements directly. `AuditFull.lean` additionally reports supporting results for other JSP problems; their successful axiom reports are **not** a mathematical/full-scope verdict for those other problems. A scan of all custom Lean source found no active proof-placeholder, custom-axiom or native-evaluation mechanism along this target's chain; the transitive axiom outputs, not keyword absence alone, support the conclusion.

## Trust and remaining decisions

This run completed static/semantic review, actual Lean/source/axiom checking and Lean's own kernel replay. `leanchecker` is not an independently implemented kernel, and no stronger claim about freshly replaying every Mathlib dependency is made. The [historical FRO/nanoda record](../2026-09-23-fro/README.md) at `4d7493e7e730597877c38bd750bf02839863b68a` concerns the same selected proof, but was not rerun here; its self-authored challenge imports submitted definitions and does not independently settle English-to-Lean correspondence. No fresh comparator/nanoda result is claimed.

All 86 original tracked Lean files, compiler pin, Lake configuration and dependency manifest remained unchanged; only the two additional untracked audit modules were added to the checking copy. [Input hashes](evidence/input-hashes.json), [post-run receipt](evidence/post-run.json) and the helper's before/after checks record this. Published logs replace absolute host paths with placeholders; [published-hashes.json](published-hashes.json) hashes those published bytes.

Attribution for the base development remains Ethan Yang / ethn-y, fixed upstream commit `03bd3e064c0b95e8e7d335fa0f3e3de0713ca777`, under the retained MIT notice. The existing same-person assertion with randyxian08 was not verified or used as an authorship premise in this audit. The `JSPInterpolation` extensions and inherited work must be assessed separately. No new identity attestation is made.

The organizers still need to determine the canonical interpretation in light of the background discrepancy, contribution/attribution, first public completion and any award eligibility. PR #765 and claim #152 have no merged-acceptance basis in this review. This proof-review supplement is placed in the existing PR; it is not a new award claim, organizer-approved challenge, or reservation of priority.
