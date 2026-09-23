import Erdos1153.JSPInterpolation.AllGaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Semantic regression checks: fixing the extreme interpolation nodes to
-1 and 1 makes the ORIGINAL all-gap objective identically one.  This is
precisely why the fixed-endpoint internal-gap result must not be substituted
for JSP-000937. Reproduce the pinned revision's checks with verify.sh. -/

namespace JSPFreeNodes
open Erdos1153 Erdos1153.DeBoorPinkus
noncomputable section

lemma one_le_internal_minPeak {d : ℕ} (nodes : NodeFamily (d + 2)) :
    1 ≤ minPeak nodes := by
  apply (le_orderedMinPeak_iff nodes.sorted 1).2
  intro i
  change 1 ≤ lebesgueOn nodes.sorted.toNodeFamily
    (nodes.sorted.point (gapLeftIndex i)) (nodes.sorted.point (gapRightIndex i))
  have hval := value_le_interval_max nodes.sorted.toNodeFamily
    (gap_left_lt_right nodes.sorted i).le
    (show nodes.sorted.point (gapLeftIndex i) ∈
      Set.Icc (nodes.sorted.point (gapLeftIndex i))
        (nodes.sorted.point (gapRightIndex i)) from
      ⟨le_rfl, (gap_left_lt_right nodes.sorted i).le⟩)
  simpa only [lebesgueFunction_at_node] using hval

/-- The all-gap minimum of EVERY endpoint-fixed node array is exactly one,
regardless of whether its internal peaks equioscillate. -/
theorem canonical_allMinPeak_eq_one {d : ℕ} (opt : EndpointArray d (-1) 1) :
    allMinPeak opt.toNodeFamily = 1 := by
  have hl : lebesgueFunction opt.toNodeFamily (-1) = 1 := by
    calc
      lebesgueFunction opt.toNodeFamily (-1) =
          lebesgueFunction opt.toNodeFamily (opt.point (endpointLeftIndex d)) :=
        congrArg (lebesgueFunction opt.toNodeFamily) opt.left_endpoint.symm
      _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointLeftIndex d)
  have hr : lebesgueFunction opt.toNodeFamily 1 = 1 := by
    calc
      lebesgueFunction opt.toNodeFamily 1 =
          lebesgueFunction opt.toNodeFamily (opt.point (endpointRightIndex d)) :=
        congrArg (lebesgueFunction opt.toNodeFamily) opt.right_endpoint.symm
      _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointRightIndex d)
  rw [allMinPeak_eq_min, hl, hr]
  rw [min_eq_right (one_le_internal_minPeak opt.toNodeFamily), min_self]

/-- Whenever the canonical internal height exceeds one, fixing the
extreme nodes gives a configuration that does NOT maximize the original
all-gap objective. -/
theorem canonical_not_full_maximizer {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (hheight : 1 < opt.height 0) :
    ¬ IsFullMaximizer opt.toNodeFamily := by
  intro hmax
  have heq := (full_maximizer_iff_eq opt hopt opt.toNodeFamily).1 hmax
  rw [canonical_allMinPeak_eq_one] at heq
  linarith

end
end JSPFreeNodes
