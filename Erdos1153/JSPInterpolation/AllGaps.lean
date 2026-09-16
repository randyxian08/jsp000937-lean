import Erdos1153.JSPInterpolation.FreeNodes
import Erdos1153.Interpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JSP-000937: the ORIGINAL all-gap maximin problem

Unlike the auxiliary internal-gap maximin problem, Erdős 1130 includes
[-1,x_first] and [x_last,1].  The proof below includes both intervals,
proves attainment by an explicitly compressed pattern, and classifies
all maximizers.  The independent logarithmic-growth request is separately
named in Definitions.lean; this file does not silently assume that request.

STATUS: newly written proof-body candidate, NOT compiler-verified here.
-/

namespace JSPFreeNodes
open Erdos1153 Erdos1153.DeBoorPinkus
noncomputable section

lemma allMinPeak_le {d : ℕ} (nodes : NodeFamily (d + 2))
    (i : Option (Option (Fin (d + 1)))) :
    allMinPeak nodes ≤ augmentedGapHeight nodes i := by
  classical
  exact csInf_le (Set.finite_range (augmentedGapHeight nodes)).bddBelow
    (Set.mem_range_self i)

lemma le_allMinPeak_iff {d : ℕ} (nodes : NodeFamily (d + 2)) (L : ℝ) :
    L ≤ allMinPeak nodes ↔ ∀ i, L ≤ augmentedGapHeight nodes i := by
  constructor
  · intro h i
    exact h.trans (allMinPeak_le nodes i)
  · intro h
    apply le_csInf
    · exact ⟨augmentedGapHeight nodes none, ⟨none, rfl⟩⟩
    · rintro _ ⟨i, rfl⟩
      exact h i

/-- Neither endpoint is inserted into the interpolating node family. The
maximum on each exterior interval is attained at the ambient endpoint. -/
lemma left_exterior_max {d : ℕ} (nodes : NodeFamily (d + 2)) :
    lebesgueOn nodes (-1) (nodes.sorted.point 0) =
      lebesgueFunction nodes (-1) := by
  have hab : (-1 : ℝ) ≤ nodes.sorted.point 0 := nodes.sorted.neg_one_le 0
  apply le_antisymm
  · apply (interval_max_le_iff nodes hab).2
    intro x hx
    have hxj (j : Fin (d + 2)) : x ≤ nodes.point j := by
      obtain ⟨i, hi⟩ := nodes.sortingPerm.surjective j
      rw [← hi, NodeFamily.point_sortingPerm]
      exact hx.2.trans (nodes.sorted.strictMono.monotone (Fin.zero_le i))
    exact lebesgue_left_exterior nodes hx.1 hxj
  · exact value_le_interval_max nodes hab ⟨le_rfl, hab⟩

lemma right_exterior_max {d : ℕ} (nodes : NodeFamily (d + 2)) :
    lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1 =
      lebesgueFunction nodes 1 := by
  have hab : nodes.sorted.point (Fin.last (d + 1)) ≤ (1 : ℝ) :=
    nodes.sorted.le_one _
  apply le_antisymm
  · apply (interval_max_le_iff nodes hab).2
    intro x hx
    have hjx (j : Fin (d + 2)) : nodes.point j ≤ x := by
      obtain ⟨i, hi⟩ := nodes.sortingPerm.surjective j
      rw [← hi, NodeFamily.point_sortingPerm]
      exact (nodes.sorted.strictMono.monotone (Fin.le_last i)).trans hx.1
    exact lebesgue_right_exterior nodes hx.2 hjx
  · exact value_le_interval_max nodes hab ⟨hab, le_rfl⟩

lemma allMinPeak_le_internal {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ minPeak nodes := by
  apply (le_orderedMinPeak_iff nodes.sorted _).2
  intro i
  exact allMinPeak_le nodes (some (some i))

/-- The literal minimum over n+1 intervals is exactly the three-way minimum
of the left exterior peak, the internal-gap minimum, and the right exterior peak. -/
lemma allMinPeak_eq_min {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes = min (lebesgueFunction nodes (-1))
      (min (minPeak nodes) (lebesgueFunction nodes 1)) := by
  apply le_antisymm
  · apply le_min
    · simpa only [augmentedGapHeight, left_exterior_max] using allMinPeak_le nodes none
    · apply le_min
      · exact allMinPeak_le_internal nodes
      · simpa only [augmentedGapHeight, right_exterior_max] using
          allMinPeak_le nodes (some none)
  · apply (le_allMinPeak_iff nodes _).2
    intro i
    cases i with
    | none =>
      simpa only [augmentedGapHeight, left_exterior_max] using
        (min_le_left (lebesgueFunction nodes (-1))
          (min (minPeak nodes) (lebesgueFunction nodes 1)))
    | some j =>
      cases j with
      | none =>
        change min (lebesgueFunction nodes (-1))
          (min (minPeak nodes) (lebesgueFunction nodes 1)) ≤
          lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1
        rw [right_exterior_max]
        exact (min_le_right _ _).trans (min_le_right _ _)
      | some g =>
        exact (min_le_right _ _).trans
          ((min_le_left _ _).trans (orderedMinPeak_le nodes.sorted g))

lemma allMinPeak_upper_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ opt.height 0 :=
  (allMinPeak_le_internal nodes).trans (minPeak_upper_bound opt hopt nodes)

lemma allMinPeak_eq_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes = opt.height 0 ↔
      HasShape opt nodes ∧
      opt.height 0 ≤ lebesgueFunction nodes (-1) ∧
      opt.height 0 ≤ lebesgueFunction nodes 1 := by
  constructor
  · intro heq
    have hle : opt.height 0 ≤ allMinPeak nodes := heq.ge
    have hleft := (le_allMinPeak_iff nodes _).1 hle none
    have hright := (le_allMinPeak_iff nodes _).1 hle (some none)
    have hint : minPeak nodes = opt.height 0 :=
      le_antisymm (minPeak_upper_bound opt hopt nodes)
        (hle.trans (allMinPeak_le_internal nodes))
    refine ⟨(minPeak_eq_iff_shape opt hopt nodes).1 hint, ?_, ?_⟩
    · simpa only [augmentedGapHeight, left_exterior_max] using hleft
    · simpa only [augmentedGapHeight, right_exterior_max] using hright
  · rintro ⟨hshape, hleft, hright⟩
    apply le_antisymm (allMinPeak_upper_bound opt hopt nodes)
    rw [allMinPeak_eq_min]
    apply le_min hleft
    apply le_min
    · exact ((minPeak_eq_iff_shape opt hopt nodes).2 hshape).ge
    · exact hright

/-! ## Actual attainment, not an unproved assumption about exterior growth -/

/-- Exactness of interpolation for p(X)=X bounds the exterior Lebesgue
function below whenever every node lies in [-a,a]. -/
lemma abs_le_scale_mul_lebesgue {d : ℕ} (nodes : NodeFamily (d + 2))
    (a x : ℝ) (ha : ∀ k, |nodes.point k| ≤ a) :
    |x| ≤ a * lebesgueFunction nodes x := by
  have hp : (Polynomial.X : Polynomial ℝ).degree < (d + 2 : ℕ) := by
    rw [Polynomial.degree_X]
    exact_mod_cast (show (1 : ℕ) < d + 2 by omega)
  simpa only [Polynomial.eval_X] using
    (abs_eval_le_mul_lebesgueFunction nodes Polynomial.X hp a x
      (by simpa only [Polynomial.eval_X] using ha))

/-- An explicit compression of the equioscillating pattern attains the
all-gap optimum.  No divergent-limit theorem or selection assumption is used. -/
lemma exists_allMinPeak_eq {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) :
    ∃ nodes : NodeFamily (d + 2), allMinPeak nodes = opt.height 0 := by
  let R : ℝ := |opt.height 0| + 2
  let a : ℝ := 1 / R
  have hR : 1 < R := by dsimp [R]; linarith [abs_nonneg (opt.height 0)]
  have hRpos : 0 < R := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact (div_le_iff₀ hRpos).2 (by linarith)
  have hAR : a * R = 1 := by
    dsimp [a]
    field_simp [ne_of_gt hRpos]
  have hab : AdmissibleInterval (-a) a := by
    exact ⟨by linarith, by linarith, ha1⟩
  let compressed : EndpointArray d (-a) a := affineNodes opt hab
  have hpoint (k : Fin (d + 2)) : compressed.point k = a * opt.point k := by
    change affine (-a) a (opt.point k) = _
    unfold affine
    ring
  have hsmall (k : Fin (d + 2)) : |compressed.point k| ≤ a := by
    rw [hpoint, abs_mul, abs_of_pos ha]
    have hk : |opt.point k| ≤ 1 := abs_le.mpr (opt.mem_Icc k)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hk ha.le
  have hshape : HasShape opt compressed.toNodeFamily := by
    unfold HasShape
    rw [sorted_endpoint_array]
    intro k
    have hl : left compressed.toOrderedNodes = -a := compressed.left_endpoint
    have hr : right compressed.toOrderedNodes = a := compressed.right_endpoint
    rw [hl, hr]
    rfl
  have hendpoint (x : ℝ) (hx : |x| = 1) :
      opt.height 0 ≤ lebesgueFunction compressed.toNodeFamily x := by
    have hxbound := abs_le_scale_mul_lebesgue compressed.toNodeFamily a x hsmall
    rw [hx] at hxbound
    have hRR : R ≤ lebesgueFunction compressed.toNodeFamily x := by
      by_contra h
      have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge h) ha
      rw [hAR] at hlt
      linarith
    exact (by dsimp [R]; linarith [le_abs_self (opt.height 0)] : opt.height 0 ≤ R).trans hRR
  refine ⟨compressed.toNodeFamily,
    (allMinPeak_eq_iff_shape_and_endpoints opt hopt compressed.toNodeFamily).2 ?_⟩
  exact ⟨hshape, hendpoint (-1) (by norm_num), hendpoint 1 (by norm_num)⟩

lemma full_maximizer_iff_eq {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    IsFullMaximizer nodes ↔ allMinPeak nodes = opt.height 0 := by
  constructor
  · intro hmax
    obtain ⟨witness, hwitness⟩ := exists_allMinPeak_eq opt hopt
    apply le_antisymm (allMinPeak_upper_bound opt hopt nodes)
    rw [← hwitness]
    exact hmax witness
  · intro heq other
    rw [heq]
    exact allMinPeak_upper_bound opt hopt other

lemma full_maximizer_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    IsFullMaximizer nodes ↔
      HasShape opt nodes ∧
      opt.height 0 ≤ lebesgueFunction nodes (-1) ∧
      opt.height 0 ≤ lebesgueFunction nodes 1 :=
  (full_maximizer_iff_eq opt hopt nodes).trans
    (allMinPeak_eq_iff_shape_and_endpoints opt hopt nodes)

lemma oneNodeAllMinPeak_eq_one (nodes : NodeFamily 1) :
    oneNodeAllMinPeak nodes = 1 := by
  have hmax {a b : ℝ} (hab : a ≤ b) : lebesgueOn nodes a b = 1 := by
    obtain ⟨t, _ht, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    exact heq.trans (single_node_lebesgue nodes t)
  unfold oneNodeAllMinPeak
  rw [hmax (nodes.mem_Icc 0).1, hmax (nodes.mem_Icc 0).2, min_self]

theorem jsp_000937_one_node (nodes : NodeFamily 1) : IsOneNodeFullMaximizer nodes := by
  intro other
  calc
    oneNodeAllMinPeak other = 1 := oneNodeAllMinPeak_eq_one other
    _ ≤ 1 := le_rfl
    _ = oneNodeAllMinPeak nodes := (oneNodeAllMinPeak_eq_one nodes).symm

/-- Complete classification for the actual all-gap maximization. This theorem
has no fixed-endpoint hypotheses on any competitor. -/
theorem jsp_000937_classification : Target937Classification := by
  constructor
  · exact jsp_000937_one_node
  · intro d
    obtain ⟨opt, hopt, _hunique⟩ :=
      existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
    refine ⟨opt.toNodeFamily, canonical_is_normalized opt hopt, ?_, ?_⟩
    · obtain ⟨witness, hwitness⟩ := exists_allMinPeak_eq opt hopt
      refine ⟨witness, (full_maximizer_iff_eq opt hopt witness).2 hwitness, ?_⟩
      rw [canonical_amplification opt hopt]
      exact hwitness
    · intro nodes
      rw [canonical_amplification opt hopt]
      constructor
      · exact allMinPeak_upper_bound opt hopt nodes
      · rw [← hasShape_iff_admissibleAffineCopy opt nodes]
        exact full_maximizer_iff_shape_and_endpoints opt hopt nodes

/-- A useful unconditional transfer theorem: the minimum peak of ANY node
array is no greater than the global Lebesgue constant of ANY competing
node array of the same cardinality. -/
theorem allMinPeak_le_any_amplification {d : ℕ}
    (nodes competitor : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ amplification competitor := by
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  exact (allMinPeak_upper_bound opt hopt nodes).trans
    (amplification_lower_bound opt hopt competitor)

end
end JSPFreeNodes
