import Erdos1153.DeBoorPinkus.Package
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Canonical minimax and maximin consequences of de Boor--Pinkus

This file is only the fixed-endpoint lemma layer.  The public free-node
statements are in `Erdos1153.JSPInterpolation.FreeNodes`.

Upstream: Ethan Yang, ethn-y/erdos-1153-lean,
03bd3e064c0b95e8e7d335fa0f3e3de0713ca777 (MIT).

Verification for the pinned revision is recorded in README.md and can be
reproduced with verify.sh.
-/

namespace JSPInterpolation

open Erdos1153 Erdos1153.DeBoorPinkus

noncomputable section

/-- No array other than the equioscillating array has all peaks at or below
its common height. This is the equality/uniqueness statement for minimax. -/
theorem upper_threshold_iff
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) :
    (∀ i, s.height i ≤ opt.height 0) ↔ s = opt := by
  constructor
  · intro h
    apply (comparisonPackage d A B).gapHeight_le_rigidity s opt
    intro i
    rw [hopt i 0]
    exact h i
  · intro h
    subst s
    intro i
    exact (hopt i 0).le

/-- No array other than the equioscillating array has all peaks at or above
its common height. This is the equality/uniqueness statement for maximin. -/
theorem lower_threshold_iff
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) :
    (∀ i, opt.height 0 ≤ s.height i) ↔ s = opt := by
  constructor
  · intro h
    have heq : opt = s := by
      apply (comparisonPackage d A B).gapHeight_le_rigidity opt s
      intro i
      rw [hopt i 0]
      exact h i
    exact heq.symm
  · intro h
    subst s
    intro i
    exact (hopt i 0).symm.le

/-- The optimal common peak is no larger than ANY upper bound for the
peaks of ANY competitor. In particular it is no larger than their maximum. -/
theorem optimal_le_any_peak_upper_bound
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (U : ℝ)
    (hU : ∀ i, s.height i ≤ U) :
    opt.height 0 ≤ U := by
  classical
  by_contra h
  have hlt : U < opt.height 0 := lt_of_not_ge h
  have heq : s = opt :=
    (upper_threshold_iff opt hopt s).mp
      (fun i => (hU i).trans hlt.le)
  have hbad := hU 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- ANY lower bound for all peaks of ANY competitor is no larger than the
optimal common peak. Apply this to the minimum of the competitor's peaks. -/
theorem any_peak_lower_bound_le_optimal
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (L : ℝ)
    (hL : ∀ i, L ≤ s.height i) :
    L ≤ opt.height 0 := by
  classical
  by_contra h
  have hlt : opt.height 0 < L := lt_of_not_ge h
  have heq : s = opt :=
    (lower_threshold_iff opt hopt s).mp
      (fun i => hlt.le.trans (hL i))
  have hbad := hL 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- A nonoptimal array has a peak strictly BELOW and a peak strictly ABOVE
the common optimal height. This proves the strict sandwich assertion. -/
theorem strict_peak_sandwich
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (hne : s ≠ opt) :
    (∃ i, s.height i < opt.height 0) ∧
      (∃ j, opt.height 0 < s.height j) := by
  classical
  constructor
  · by_contra h
    have hbound : ∀ i, opt.height 0 ≤ s.height i := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    exact hne ((lower_threshold_iff opt hopt s).mp hbound)
  · by_contra h
    have hbound : ∀ i, s.height i ≤ opt.height 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    exact hne ((upper_threshold_iff opt hopt s).mp hbound)

/-- Existence, minimax uniqueness, and maximin uniqueness for the canonical
arrays with extreme nodes -1 and 1. The number of nodes is d+2. -/
theorem jsp_000936_000937_canonical (d : ℕ) :
    ∃ opt : EndpointArray d (-1 : ℝ) 1,
      Equioscillates opt ∧
      ∀ s : EndpointArray d (-1 : ℝ) 1,
        ((∀ i, s.height i ≤ opt.height 0) ↔ s = opt) ∧
        ((∀ i, opt.height 0 ≤ s.height i) ↔ s = opt) := by
  have hAB : AdmissibleInterval (-1 : ℝ) 1 := by
    norm_num [AdmissibleInterval]
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1 : ℝ) 1 hAB
  refine ⟨opt, hopt, ?_⟩
  intro s
  exact ⟨upper_threshold_iff opt hopt s,
    lower_threshold_iff opt hopt s⟩

end

end JSPInterpolation
