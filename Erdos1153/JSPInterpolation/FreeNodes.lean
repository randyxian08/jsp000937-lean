import Erdos1153.JSPInterpolation.Definitions
import Erdos1153.JSPInterpolation.Canonical
import Erdos1153.ClassicalBound.EquioscillatingHeight
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JSP-000936 / JSP-000937: arbitrary, freely chosen interpolation nodes

Every public competitor below has type `NodeFamily (d + 2)`.  Its only
constraints are pairwise distinctness and membership in [-1,1].  There is
NO assumption that the extreme nodes equal -1 and 1, or that the original
enumeration is increasing.

The canonical endpoint array is a reference shape, not a restriction on
competitors.  Sorting, affine transport, both exterior intervals, the
actual maximum, and the actual minimum of the gap maxima are addressed.

The difficult de Boor--Pinkus theorem is imported from Ethan Yang's pinned
MIT-licensed project; it is not postulated as a new axiom here.

NEW CODE STATUS: complete proof-body candidate; NOT compiler-verified in
the authoring environment.  Run the supplied verify.sh before treating
these declarations as checked Lean theorems.
-/

namespace JSPFreeNodes

open Erdos1153 Erdos1153.DeBoorPinkus

noncomputable section

/-! ## Elementary maximum and finite-minimum interfaces -/

lemma value_le_interval_max {n : ℕ} (nodes : NodeFamily n)
    {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    lebesgueFunction nodes x ≤ lebesgueOn nodes a b := by
  obtain ⟨t, _ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [heq]
  exact hmax x hx

lemma interval_max_le_iff {n : ℕ} (nodes : NodeFamily n)
    {a b U : ℝ} (hab : a ≤ b) :
    lebesgueOn nodes a b ≤ U ↔
      ∀ x ∈ Set.Icc a b, lebesgueFunction nodes x ≤ U := by
  constructor
  · intro h x hx
    exact (value_le_interval_max nodes hab hx).trans h
  · intro h
    obtain ⟨t, ht, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    rw [heq]
    exact h t ht

lemma orderedMinPeak_le {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) : orderedMinPeak nodes ≤ gapHeight nodes i := by
  classical
  exact csInf_le (Set.finite_range (fun j : Fin (d + 1) => gapHeight nodes j)).bddBelow
    (Set.mem_range_self i)

lemma le_orderedMinPeak_iff {d : ℕ} (nodes : OrderedNodes (d + 2)) (L : ℝ) :
    L ≤ orderedMinPeak nodes ↔ ∀ i : Fin (d + 1), L ≤ gapHeight nodes i := by
  constructor
  · intro h i
    exact h.trans (orderedMinPeak_le nodes i)
  · intro h
    apply le_csInf
    · exact ⟨gapHeight nodes (0 : Fin (d + 1)), ⟨0, rfl⟩⟩
    · rintro _ ⟨i, rfl⟩
      exact h i

lemma gap_le_amplification {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) : gapHeight nodes i ≤ amplification nodes.toNodeFamily := by
  change lebesgueOn nodes.toNodeFamily
      (nodes.point (gapLeftIndex i)) (nodes.point (gapRightIndex i)) ≤
    lebesgueOn nodes.toNodeFamily (-1) 1
  apply (interval_max_le_iff nodes.toNodeFamily (gap_left_lt_right nodes i).le).2
  intro x hx
  apply value_le_interval_max nodes.toNodeFamily (by norm_num)
  exact ⟨(nodes.neg_one_le _).trans hx.1, hx.2.trans (nodes.le_one _)⟩

/-! ## Sorting does not remove or constrain any node configurations -/

lemma ordered_ext {n : ℕ} {s t : OrderedNodes n}
    (h : ∀ i, s.point i = t.point i) : s = t := by
  have hbase : s.toNodeFamily = t.toNodeFamily := NodeFamily.ext (funext h)
  cases s
  cases t
  cases hbase
  rfl

lemma sorted_ordered_point {n : ℕ} (s : OrderedNodes n) (i : Fin n) :
    s.toNodeFamily.sorted.point i = s.point i := by
  have h := Finset.orderEmbOfFin_unique
    (NodeFamily.card_nodeFinset s.toNodeFamily)
    (fun k => (NodeFamily.mem_nodeFinset s.toNodeFamily _).2 ⟨k, rfl⟩)
    s.strictMono
  exact (congrFun h i).symm

@[simp]
lemma sorted_of_ordered {n : ℕ} (s : OrderedNodes n) :
    s.toNodeFamily.sorted = s :=
  ordered_ext (sorted_ordered_point s)

@[simp]
lemma sorted_endpoint_array {d : ℕ} {A B : ℝ} (s : EndpointArray d A B) :
    s.toNodeFamily.sorted = s.toOrderedNodes :=
  sorted_of_ordered s.toOrderedNodes

lemma amplification_sorted {n : ℕ} (nodes : NodeFamily n) :
    amplification nodes.sorted.toNodeFamily = amplification nodes :=
  NodeFamily.lebesgueOn_sorted nodes (-1) 1

/-! ## The actual extreme nodes, which are NOT assumed to be -1 and 1 -/

def left {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  nodes.point (endpointLeftIndex d)

def right {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  nodes.point (endpointRightIndex d)

/-- Regard a free ordered family as an endpoint array at its OWN endpoints. -/
def frame {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    EndpointArray d (left nodes) (right nodes) where
  toOrderedNodes := nodes
  left_endpoint := rfl
  right_endpoint := rfl

lemma left_le_point {d : ℕ} (nodes : OrderedNodes (d + 2)) (i : Fin (d + 2)) :
    left nodes ≤ nodes.point i := by
  apply nodes.strictMono.monotone
  change (endpointLeftIndex d).val ≤ i.val
  simp

lemma point_le_right {d : ℕ} (nodes : OrderedNodes (d + 2)) (i : Fin (d + 2)) :
    nodes.point i ≤ right nodes := by
  apply nodes.strictMono.monotone
  change i.val ≤ (endpointRightIndex d).val
  simp only [endpointRightIndex_val]
  omega

/-! ## A genuine affine bijection, and transport of the literal products -/

/-- The increasing affine map taking -1 to A and 1 to B. -/
def affine (A B t : ℝ) : ℝ :=
  (A + B) / 2 + ((B - A) / 2) * t

/-- Its inverse when A < B. -/
def unaffine (A B x : ℝ) : ℝ :=
  (x - (A + B) / 2) / ((B - A) / 2)

@[simp]
lemma affine_neg_one (A B : ℝ) : affine A B (-1) = A := by
  unfold affine
  ring

@[simp]
lemma affine_one (A B : ℝ) : affine A B 1 = B := by
  unfold affine
  ring

lemma affine_strictMono {A B : ℝ} (hAB : A < B) : StrictMono (affine A B) := by
  have hs : (0 : ℝ) < (B - A) / 2 := by linarith
  intro u v huv
  change (A + B) / 2 + ((B - A) / 2) * u <
    (A + B) / 2 + ((B - A) / 2) * v
  simpa only [add_comm] using
    (add_lt_add_left (mul_lt_mul_of_pos_left huv hs) ((A + B) / 2))

lemma affine_unaffine {A B : ℝ} (hAB : A < B) (x : ℝ) :
    affine A B (unaffine A B x) = x := by
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hcancel (c s : ℝ) (hs' : s ≠ 0) : c + s * ((x - c) / s) = x := by
    field_simp [hs']
    <;> ring
  exact hcancel _ _ hs

lemma unaffine_affine {A B : ℝ} (hAB : A < B) (t : ℝ) :
    unaffine A B (affine A B t) = t := by
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hcancel (c s : ℝ) (hs' : s ≠ 0) : (c + s * t - c) / s = t := by
    field_simp [hs']
    <;> ring
  exact hcancel _ _ hs

lemma affine_mem_Icc {A B u v t : ℝ} (hAB : A < B)
    (ht : t ∈ Set.Icc u v) : affine A B t ∈ Set.Icc (affine A B u) (affine A B v) :=
  ⟨(affine_strictMono hAB).monotone ht.1, (affine_strictMono hAB).monotone ht.2⟩

lemma unaffine_mem_Icc {A B u v x : ℝ} (hAB : A < B)
    (hx : x ∈ Set.Icc (affine A B u) (affine A B v)) :
    unaffine A B x ∈ Set.Icc u v := by
  constructor
  · by_contra h
    have hlt := affine_strictMono hAB (lt_of_not_ge h)
    rw [affine_unaffine hAB x] at hlt
    exact (not_lt_of_ge hx.1) hlt
  · by_contra h
    have hlt := affine_strictMono hAB (lt_of_not_ge h)
    rw [affine_unaffine hAB x] at hlt
    exact (not_lt_of_ge hx.2) hlt

/-- An actual affine copy of the canonical array in ANY admissible [A,B]. -/
def affineNodes {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) : EndpointArray d A B where
  point i := affine A B (opt.point i)
  injective := (affine_strictMono hAB.2.1).injective.comp opt.injective
  mem_Icc i := by
    have hi := affine_mem_Icc hAB.2.1 (opt.mem_Icc i)
    rw [affine_neg_one, affine_one] at hi
    exact ⟨hAB.1.trans hi.1, hi.2.trans hAB.2.2⟩
  strictMono := (affine_strictMono hAB.2.1).comp opt.strictMono
  left_endpoint := by rw [opt.left_endpoint, affine_neg_one]
  right_endpoint := by rw [opt.right_endpoint, affine_one]

@[simp]
lemma affineNodes_point {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (i : Fin (d + 2)) :
    (affineNodes opt hAB).point i = affine A B (opt.point i) := rfl

lemma lagrangeFundamental_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (k : Fin (d + 2)) (t : ℝ) :
    lagrangeFundamental (affineNodes opt hAB).toNodeFamily k (affine A B t) =
      lagrangeFundamental opt.toNodeFamily k t := by
  classical
  unfold lagrangeFundamental
  apply Finset.prod_congr rfl
  intro j _hj
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith [hAB.2.1])
  change (affine A B t - affine A B (opt.point j)) /
      (affine A B (opt.point k) - affine A B (opt.point j)) =
    (t - opt.point j) / (opt.point k - opt.point j)
  have hdiff (u v : ℝ) : affine A B u - affine A B v = ((B - A) / 2) * (u - v) := by
    unfold affine
    ring
  rw [hdiff, hdiff]
  -- Cancel the common nonzero slope directly.  No field_simp normalization
  -- or polynomial reasoning about an inverse of B-A is needed.
  exact mul_div_mul_left _ _ hs

lemma lebesgueFunction_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (t : ℝ) :
    lebesgueFunction (affineNodes opt hAB).toNodeFamily (affine A B t) =
      lebesgueFunction opt.toNodeFamily t := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro k _hk
  rw [lagrangeFundamental_affine]

/-- Invariance of interval maxima, proved by transporting both maximizers. -/
lemma lebesgueOn_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) {a b : ℝ} (hab : a ≤ b) :
    lebesgueOn (affineNodes opt hAB).toNodeFamily (affine A B a) (affine A B b) =
      lebesgueOn opt.toNodeFamily a b := by
  obtain ⟨u, hu, hu_eq, hu_max⟩ := exists_lebesgueOn_eq_and_ge
    (affineNodes opt hAB).toNodeFamily ((affine_strictMono hAB.2.1).monotone hab)
  obtain ⟨t, ht, ht_eq, ht_max⟩ := exists_lebesgueOn_eq_and_ge opt.toNodeFamily hab
  apply le_antisymm
  · rw [hu_eq, ht_eq]
    have hv := unaffine_mem_Icc hAB.2.1 hu
    rw [← affine_unaffine hAB.2.1 u, lebesgueFunction_affine]
    exact ht_max (unaffine A B u) hv
  · rw [hu_eq, ht_eq]
    have h := hu_max (affine A B t) (affine_mem_Icc hAB.2.1 ht)
    rw [lebesgueFunction_affine] at h
    exact h

lemma height_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (i : Fin (d + 1)) :
    (affineNodes opt hAB).height i = opt.height i := by
  unfold EndpointArray.height gapHeight
  simpa only [affineNodes_point] using
    (lebesgueOn_affine opt hAB (gap_left_lt_right opt.toOrderedNodes i).le)

lemma equioscillates_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) {A B : ℝ} (hAB : AdmissibleInterval A B) :
    Equioscillates (affineNodes opt hAB) := by
  intro i j
  rw [height_affine, height_affine]
  exact hopt i j

/-! ## Explicit affine shape, and its equivalent c + scale*x description -/

/-- Only the relative positions are fixed. The two extreme nodes are free. -/
def HasShape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) : Prop :=
  ∀ i, nodes.sorted.point i =
    affine (left nodes.sorted) (right nodes.sorted) (opt.point i)

lemma frame_eq_affine_iff {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    frame nodes.sorted = affineNodes opt (frame nodes.sorted).admissibleInterval ↔
      HasShape opt nodes := by
  constructor
  · intro h i
    exact congrArg (fun s : EndpointArray d (left nodes.sorted) (right nodes.sorted) =>
      s.point i) h
  · intro h
    apply EndpointArray.ext
    exact h

/-- The shape condition is literally a positive affine image fitting in [-1,1]. -/
lemma hasShape_iff_affine_copy {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    HasShape opt nodes ↔
      ∃ c scale : ℝ, 0 < scale ∧ |c| + scale ≤ 1 ∧
        ∀ i, nodes.sorted.point i = c + scale * opt.point i := by
  constructor
  · intro h
    let a := left nodes.sorted
    let b := right nodes.sorted
    let c := (a + b) / 2
    let scale := (b - a) / 2
    have hab : a < b := (frame nodes.sorted).endpoints_lt
    have ha : -1 ≤ a := (frame nodes.sorted).neg_one_le_left
    have hb : b ≤ 1 := (frame nodes.sorted).right_le_one
    refine ⟨c, scale, ?_, ?_, ?_⟩
    · dsimp [scale]
      linarith
    · rcases le_total 0 c with hc | hc
      · rw [abs_of_nonneg hc]
        dsimp [c, scale]
        linarith
      · rw [abs_of_nonpos hc]
        dsimp [c, scale]
        linarith
    · exact h
  · rintro ⟨c, scale, _hscale, _hfit, hpoints⟩
    have ha := hpoints (endpointLeftIndex d)
    have hb := hpoints (endpointRightIndex d)
    rw [opt.left_endpoint] at ha
    rw [opt.right_endpoint] at hb
    change left nodes.sorted = c + scale * (-1) at ha
    change right nodes.sorted = c + scale * 1 at hb
    have hc : (left nodes.sorted + right nodes.sorted) / 2 = c := by linarith
    have hs : (right nodes.sorted - left nodes.sorted) / 2 = scale := by linarith
    intro i
    change nodes.sorted.point i =
      (left nodes.sorted + right nodes.sorted) / 2 +
        ((right nodes.sorted - left nodes.sorted) / 2) * opt.point i
    rw [hc, hs]
    exact hpoints i

/-! ## Bounds that already range over every free-node family -/

lemma canonical_amplification {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) :
    amplification opt.toNodeFamily = opt.height 0 :=
  ClassicalBound.lebesgueOn_eq_height_zero_of_equioscillates opt hopt

lemma ordered_amplification_lower_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : OrderedNodes (d + 2)) :
    opt.height 0 ≤ amplification nodes.toNodeFamily := by
  have h := JSPInterpolation.optimal_le_any_peak_upper_bound
    (affineNodes opt (frame nodes).admissibleInterval)
    (equioscillates_affine opt hopt (frame nodes).admissibleInterval)
    (frame nodes) (amplification nodes.toNodeFamily)
    (fun i => gap_le_amplification nodes i)
  simpa only [height_affine] using h

lemma amplification_lower_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    opt.height 0 ≤ amplification nodes := by
  have h := ordered_amplification_lower_bound opt hopt nodes.sorted
  rwa [amplification_sorted] at h

lemma minPeak_upper_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    minPeak nodes ≤ opt.height 0 := by
  have h := JSPInterpolation.any_peak_lower_bound_le_optimal
    (affineNodes opt (frame nodes.sorted).admissibleInterval)
    (equioscillates_affine opt hopt (frame nodes.sorted).admissibleInterval)
    (frame nodes.sorted) (minPeak nodes)
    (fun i => orderedMinPeak_le nodes.sorted i)
  simpa only [height_affine] using h

lemma canonical_minPeak {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) : minPeak opt.toNodeFamily = opt.height 0 := by
  change orderedMinPeak opt.toOrderedNodes.toNodeFamily.sorted = opt.height 0
  rw [sorted_of_ordered]
  apply le_antisymm
  · exact orderedMinPeak_le opt.toOrderedNodes 0
  · apply (le_orderedMinPeak_iff opt.toOrderedNodes (opt.height 0)).2
    intro i
    exact (hopt i 0).symm.le

/-! ## Auxiliary internal-gap equality classification -/

lemma minPeak_eq_iff_shape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    minPeak nodes = opt.height 0 ↔ HasShape opt nodes := by
  constructor
  · intro hmin
    apply (frame_eq_affine_iff opt nodes).1
    apply (JSPInterpolation.lower_threshold_iff
      (affineNodes opt (frame nodes.sorted).admissibleInterval)
      (equioscillates_affine opt hopt (frame nodes.sorted).admissibleInterval)
      (frame nodes.sorted)).1
    intro i
    rw [height_affine, ← hmin]
    exact orderedMinPeak_le nodes.sorted i
  · intro hshape
    have heq := (frame_eq_affine_iff opt nodes).2 hshape
    apply le_antisymm (minPeak_upper_bound opt hopt nodes)
    apply (le_orderedMinPeak_iff nodes.sorted (opt.height 0)).2
    intro i
    change opt.height 0 ≤ (frame nodes.sorted).height i
    rw [heq, height_affine]
    exact (hopt i 0).symm.le

lemma maximizer_iff_shape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    IsInternalMaximizer nodes ↔ HasShape opt nodes := by
  rw [← minPeak_eq_iff_shape opt hopt nodes]
  constructor
  · intro h
    apply le_antisymm (minPeak_upper_bound opt hopt nodes)
    have h' := h opt.toNodeFamily
    rwa [canonical_minPeak opt hopt] at h'
  · intro h other
    rw [h]
    exact minPeak_upper_bound opt hopt other

/-! ## Exterior intervals: upper tests for 936, lower tests for 937 -/

/-- To the left of all nodes, moving farther left can only increase the
Lebesgue function.  This is proved factor by factor, not assumed. -/
lemma lebesgue_left_exterior {n : ℕ} (nodes : NodeFamily n) {u v : ℝ}
    (huv : u ≤ v) (hv : ∀ i, v ≤ nodes.point i) :
    lebesgueFunction nodes v ≤ lebesgueFunction nodes u := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_le_sum
  intro k _hk
  simp only [lagrangeFundamental, Finset.abs_prod, abs_div]
  apply Finset.prod_le_prod
  · intro j _hj
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j _hj
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonpos (sub_nonpos.mpr (hv j)),
      abs_of_nonpos (sub_nonpos.mpr (huv.trans (hv j)))]
    linarith

/-- To the right of all nodes, moving farther right can only increase the
Lebesgue function. -/
lemma lebesgue_right_exterior {n : ℕ} (nodes : NodeFamily n) {u v : ℝ}
    (huv : u ≤ v) (hu : ∀ i, nodes.point i ≤ u) :
    lebesgueFunction nodes u ≤ lebesgueFunction nodes v := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_le_sum
  intro k _hk
  simp only [lagrangeFundamental, Finset.abs_prod, abs_div]
  apply Finset.prod_le_prod
  · intro j _hj
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j _hj
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonneg (sub_nonneg.mpr (hu j)),
      abs_of_nonneg (sub_nonneg.mpr ((hu j).trans huv))]
    exact sub_le_sub_right huv _

/-- Pointwise control on the WHOLE ambient interval from all internal peaks
and the two ambient endpoint values. -/
lemma full_interval_bound_of_gaps_and_endpoints {d : ℕ}
    (nodes : OrderedNodes (d + 2)) (U : ℝ)
    (hgaps : ∀ i : Fin (d + 1), gapHeight nodes i ≤ U)
    (hleft : lebesgueFunction nodes.toNodeFamily (-1) ≤ U)
    (hright : lebesgueFunction nodes.toNodeFamily 1 ≤ U) :
    amplification nodes.toNodeFamily ≤ U := by
  apply (interval_max_le_iff nodes.toNodeFamily (by norm_num : (-1 : ℝ) ≤ 1)).2
  intro x hx
  rcases le_total x (left nodes) with hxl | hlx
  · exact (lebesgue_left_exterior nodes.toNodeFamily hx.1
      (fun i => hxl.trans (left_le_point nodes i))).trans hleft
  · rcases le_total (right nodes) x with hrx | hxr
    · exact (lebesgue_right_exterior nodes.toNodeFamily hx.2
        (fun i => (point_le_right nodes i).trans hrx)).trans hright
    · obtain ⟨i, hi⟩ := ClassicalBound.exists_closedGap_of_mem_Icc
        (frame nodes) ⟨hlx, hxr⟩
      exact (DeBoorPinkus.lebesgueFunction_le_height (frame nodes) i hi).trans (hgaps i)

/-! ## JSP-000936: exact equality classification over arbitrary node families -/

lemma amplification_eq_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    amplification nodes = opt.height 0 ↔
      HasShape opt nodes ∧
      lebesgueFunction nodes (-1) ≤ opt.height 0 ∧
      lebesgueFunction nodes 1 ≤ opt.height 0 := by
  constructor
  · intro hmax
    refine ⟨?_, ?_, ?_⟩
    · apply (frame_eq_affine_iff opt nodes).1
      apply (JSPInterpolation.upper_threshold_iff
        (affineNodes opt (frame nodes.sorted).admissibleInterval)
        (equioscillates_affine opt hopt (frame nodes.sorted).admissibleInterval)
        (frame nodes.sorted)).1
      intro i
      rw [height_affine]
      calc
        (frame nodes.sorted).height i ≤ amplification nodes.sorted.toNodeFamily :=
          gap_le_amplification nodes.sorted i
        _ = amplification nodes := amplification_sorted nodes
        _ = opt.height 0 := hmax
    · exact (value_le_interval_max nodes (by norm_num)
        (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)).trans_eq hmax
    · exact (value_le_interval_max nodes (by norm_num)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)).trans_eq hmax
  · rintro ⟨hshape, hleft, hright⟩
    have heq := (frame_eq_affine_iff opt nodes).2 hshape
    have hbound := full_interval_bound_of_gaps_and_endpoints nodes.sorted (opt.height 0)
      (fun i => by
        change (frame nodes.sorted).height i ≤ opt.height 0
        rw [heq, height_affine]
        exact (hopt i 0).le)
      (by rwa [NodeFamily.lebesgueFunction_sorted])
      (by rwa [NodeFamily.lebesgueFunction_sorted])
    rw [amplification_sorted] at hbound
    exact le_antisymm hbound (amplification_lower_bound opt hopt nodes)

lemma minimizer_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    IsMinimizer nodes ↔
      HasShape opt nodes ∧
      lebesgueFunction nodes (-1) ≤ opt.height 0 ∧
      lebesgueFunction nodes 1 ≤ opt.height 0 := by
  rw [← amplification_eq_iff_shape_and_endpoints opt hopt nodes]
  constructor
  · intro h
    apply le_antisymm _ (amplification_lower_bound opt hopt nodes)
    exact (h opt.toNodeFamily).trans_eq (canonical_amplification opt hopt)
  · intro h other
    rw [h]
    exact amplification_lower_bound opt hopt other

/-! ## A normalized-coordinate version of the two exterior tests -/

/-- Affine invariance from the literal point equations alone.  No equality
of EndpointArray structures, sorting proofs, or interval certificates is
transported through lebesgueFunction. -/
lemma lebesgueFunction_affine_of_points {n : ℕ}
    (source target : NodeFamily n) {A B : ℝ} (hAB : A < B)
    (hpoint : ∀ i, source.point i = affine A B (target.point i)) (t : ℝ) :
    lebesgueFunction source (affine A B t) = lebesgueFunction target t := by
  classical
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hdiff (u v : ℝ) :
      affine A B u - affine A B v = ((B - A) / 2) * (u - v) := by
    unfold affine
    ring
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro k _hk
  apply congrArg abs
  unfold lagrangeFundamental
  apply Finset.prod_congr rfl
  intro j _hj
  rw [hpoint j, hpoint k, hdiff, hdiff]
  exact mul_div_mul_left _ _ hs

lemma lebesgueFunction_of_shape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) (hshape : HasShape opt nodes) (t : ℝ) :
    lebesgueFunction nodes (affine (left nodes.sorted) (right nodes.sorted) t) =
      lebesgueFunction opt.toNodeFamily t := by
  calc
    lebesgueFunction nodes (affine (left nodes.sorted) (right nodes.sorted) t) =
        lebesgueFunction nodes.sorted.toNodeFamily
          (affine (left nodes.sorted) (right nodes.sorted) t) :=
      (NodeFamily.lebesgueFunction_sorted nodes _).symm
    _ = lebesgueFunction opt.toNodeFamily t :=
      lebesgueFunction_affine_of_points nodes.sorted.toNodeFamily opt.toNodeFamily
        (frame nodes.sorted).endpoints_lt hshape t

lemma lebesgueFunction_of_shape_inverse {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) (hshape : HasShape opt nodes) (x : ℝ) :
    lebesgueFunction nodes x = lebesgueFunction opt.toNodeFamily
      (unaffine (left nodes.sorted) (right nodes.sorted) x) := by
  have h := lebesgueFunction_of_shape opt nodes hshape
    (unaffine (left nodes.sorted) (right nodes.sorted) x)
  rwa [affine_unaffine (frame nodes.sorted).endpoints_lt] at h

lemma minimizer_iff_normalized_exterior_tests {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    IsMinimizer nodes ↔ HasShape opt nodes ∧
      lebesgueFunction opt.toNodeFamily
        (unaffine (left nodes.sorted) (right nodes.sorted) (-1)) ≤ opt.height 0 ∧
      lebesgueFunction opt.toNodeFamily
        (unaffine (left nodes.sorted) (right nodes.sorted) 1) ≤ opt.height 0 := by
  rw [minimizer_iff_shape_and_endpoints opt hopt nodes]
  constructor
  · rintro ⟨hs, hl, hr⟩
    exact ⟨hs, (lebesgueFunction_of_shape_inverse opt nodes hs (-1)) ▸ hl,
      (lebesgueFunction_of_shape_inverse opt nodes hs 1) ▸ hr⟩
  · rintro ⟨hs, hl, hr⟩
    exact ⟨hs, (lebesgueFunction_of_shape_inverse opt nodes hs (-1)).symm ▸ hl,
      (lebesgueFunction_of_shape_inverse opt nodes hs 1).symm ▸ hr⟩

/-! ## Public, assumption-free conclusions for the two prize problems -/

/-- JSP-000936, full free-node version: existence, optimal value, and ALL
minimizers.  The only fixed-endpoint array is the reference shape. -/
theorem jsp_000936_free (d : ℕ) :
    ∃ opt : EndpointArray d (-1) 1,
      Equioscillates opt ∧
      IsMinimizer opt.toNodeFamily ∧
      amplification opt.toNodeFamily = opt.height 0 ∧
      ∀ nodes : NodeFamily (d + 2),
        opt.height 0 ≤ amplification nodes ∧
        (IsMinimizer nodes ↔
          HasShape opt nodes ∧
          lebesgueFunction nodes (-1) ≤ opt.height 0 ∧
          lebesgueFunction nodes 1 ≤ opt.height 0) := by
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  refine ⟨opt, hopt, ?_, canonical_amplification opt hopt, ?_⟩
  · intro other
    rw [canonical_amplification opt hopt]
    exact amplification_lower_bound opt hopt other
  · intro nodes
    exact ⟨amplification_lower_bound opt hopt nodes,
      minimizer_iff_shape_and_endpoints opt hopt nodes⟩

/-- Auxiliary INTERNAL-gap maximin theorem. This is not the full
JSP-000937 objective, which also includes the two exterior intervals. -/
theorem internal_maximin_free (d : ℕ) :
    ∃ opt : EndpointArray d (-1) 1,
      Equioscillates opt ∧
      IsInternalMaximizer opt.toNodeFamily ∧
      minPeak opt.toNodeFamily = opt.height 0 ∧
      ∀ nodes : NodeFamily (d + 2),
        minPeak nodes ≤ opt.height 0 ∧
        (IsInternalMaximizer nodes ↔
          ∃ c scale : ℝ, 0 < scale ∧ |c| + scale ≤ 1 ∧
            ∀ i, nodes.sorted.point i = c + scale * opt.point i) := by
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  refine ⟨opt, hopt, ?_, canonical_minPeak opt hopt, ?_⟩
  · intro other
    rw [canonical_minPeak opt hopt]
    exact minPeak_upper_bound opt hopt other
  · intro nodes
    exact ⟨minPeak_upper_bound opt hopt nodes,
      (maximizer_iff_shape opt hopt nodes).trans (hasShape_iff_affine_copy opt nodes)⟩

/-- The n=1 edge case of minimax: every single node has amplification one.
There are no INTERNAL adjacent gaps for n=1; the all-gap extension has
two exterior intervals, each with constant Lebesgue function one. -/
lemma single_node_lebesgue (nodes : NodeFamily 1) (x : ℝ) :
    lebesgueFunction nodes x = 1 := by
  classical
  have hfund (k : Fin 1) : lagrangeFundamental nodes k x = 1 := by
    have herase : (Finset.univ : Finset (Fin 1)).erase k = ∅ := by
      apply Finset.ext
      intro j
      have hjk : j = k := Subsingleton.elim j k
      simp [hjk]
    simp only [lagrangeFundamental, herase, Finset.prod_empty]
  simp [lebesgueFunction, hfund]

lemma single_node_amplification (nodes : NodeFamily 1) :
    amplification nodes = 1 := by
  obtain ⟨x, _hx, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  exact heq.trans (single_node_lebesgue nodes x)

theorem jsp_000936_one_node (nodes : NodeFamily 1) : IsMinimizer nodes := by
  intro other
  calc
    amplification nodes = 1 := single_node_amplification nodes
    _ ≤ 1 := le_rfl
    _ = amplification other := (single_node_amplification other).symm


/-! ## Closed public targets whose competitor types contain no fixed endpoints -/

lemma canonical_is_normalized {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) : IsNormalizedEquioscillating opt.toNodeFamily := by
  unfold IsNormalizedEquioscillating
  simp only [sorted_endpoint_array]
  exact ⟨opt.left_endpoint, opt.right_endpoint, hopt⟩

lemma hasShape_iff_admissibleAffineCopy {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    HasShape opt nodes ↔ AdmissibleAffineCopy opt.toNodeFamily nodes := by
  simpa only [AdmissibleAffineCopy, sorted_of_ordered] using
    (hasShape_iff_affine_copy opt nodes)

/-- JSP-000936 in the independently stated, unrestricted-node interface. -/
theorem jsp_000936 : Target936 := by
  constructor
  · exact jsp_000936_one_node
  · intro d
    obtain ⟨opt, hopt, _hunique⟩ :=
      existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
    refine ⟨opt.toNodeFamily, canonical_is_normalized opt hopt, ?_, ?_⟩
    · intro other
      rw [canonical_amplification opt hopt]
      exact amplification_lower_bound opt hopt other
    · intro nodes
      constructor
      · rw [canonical_amplification opt hopt]
        exact amplification_lower_bound opt hopt nodes
      · rw [canonical_amplification opt hopt,
          ← hasShape_iff_admissibleAffineCopy opt nodes]
        exact minimizer_iff_shape_and_endpoints opt hopt nodes

/-- Auxiliary internal-gap problem. See AllGaps.lean for the original
JSP-000937 objective, with both exterior intervals included. -/
theorem internal_maximin : TargetInternalMaximin := by
  intro d
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  refine ⟨opt.toNodeFamily, canonical_is_normalized opt hopt, ?_, ?_⟩
  · intro other
    rw [canonical_minPeak opt hopt]
    exact minPeak_upper_bound opt hopt other
  · intro nodes
    constructor
    · rw [canonical_minPeak opt hopt]
      exact minPeak_upper_bound opt hopt nodes
    · exact (maximizer_iff_shape opt hopt nodes).trans
        (hasShape_iff_admissibleAffineCopy opt nodes)

end
end JSPFreeNodes
