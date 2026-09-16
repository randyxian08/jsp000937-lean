import Erdos1153.JSPInterpolation.Logarithmic.CardinalIdentity
import Erdos1153.JSPInterpolation.Logarithmic.HarmonicPacking
import Erdos1153.JSPInterpolation.Logarithmic.TrigonometricBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A logarithmic Lebesgue bound for an explicit competitor

The n Chebyshev root nodes cos((j+1/2)π/n) are constructed as an actual
Erdos1153.NodeFamily. The proof derives the cardinal identity from polynomial
factorization and exact interpolation, not from a stipulated formula.

The resulting bound, π + 1 + 4 H_n, is intentionally non-sharp. Its purpose is
the uniform O(log n) assertion in JSP-000937, where no sharp constant is requested.

NEW PROOF SOURCE: must be checked with Lean 4.27.0 before being called verified.
-/

namespace JSPFreeNodes.Logarithmic
open Erdos1153 Polynomial
open Polynomial.Chebyshev
open scoped BigOperators
noncomputable section

/-- The j-th equally spaced root angle. -/
def rootAngle (n : ℕ) (j : Fin n) : ℝ :=
  ((j.val : ℝ) + 1 / 2) * Real.pi / (n : ℝ)

lemma rootAngle_mem {n : ℕ} (hn : 0 < n) (j : Fin n) :
    rootAngle n j ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hjR : (j.val : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  constructor
  · unfold rootAngle
    positivity
  · unfold rootAngle
    apply (div_lt_iff₀ hnR).2
    have hlt : (j.val : ℝ) + 1 / 2 < (n : ℝ) := by linarith
    nlinarith [mul_lt_mul_of_pos_right hlt Real.pi_pos]

lemma rootAngle_mem_closed {n : ℕ} (hn : 0 < n) (j : Fin n) :
    rootAngle n j ∈ Set.Icc (0 : ℝ) Real.pi :=
  ⟨(rootAngle_mem hn j).1.le, (rootAngle_mem hn j).2.le⟩

lemma rootAngle_strictMono {n : ℕ} (hn : 0 < n) :
    StrictMono (rootAngle n) := by
  intro i j hij
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hijN : i.val < j.val := hij
  have hijR : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hijN
  unfold rootAngle
  have hadd : (i.val : ℝ) + 1 / 2 < (j.val : ℝ) + 1 / 2 := by
    linarith only [hijR]
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right hadd Real.pi_pos) hnR

/-- Actual interpolation nodes; their enumeration is decreasing, which the
public NodeFamily deliberately permits. Sorting is handled upstream. -/
def chebyshevNodes (n : ℕ) (hn : 0 < n) : NodeFamily n where
  point j := Real.cos (rootAngle n j)
  injective := by
    intro i j hij
    apply (rootAngle_strictMono hn).injective
    exact Real.injOn_cos (rootAngle_mem_closed hn i) (rootAngle_mem_closed hn j) hij
  mem_Icc j := Real.cos_mem_Icc _

@[simp] lemma chebyshevNodes_point (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (chebyshevNodes n hn).point j = Real.cos (rootAngle n j) := rfl

lemma rootAngle_sub (n : ℕ) (i j : Fin n) :
    rootAngle n i - rootAngle n j =
      ((i.val : ℝ) - (j.val : ℝ)) * (Real.pi / (n : ℝ)) := by
  unfold rootAngle
  ring

lemma cos_mul_rootAngle {n : ℕ} (hn : 0 < n) (j : Fin n) :
    Real.cos ((n : ℝ) * rootAngle n j) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply Real.cos_eq_zero_iff.mpr
  refine ⟨(j.val : ℤ), ?_⟩
  unfold rootAngle
  push_cast
  field_simp [hnR] <;> ring

lemma abs_sin_mul_rootAngle {n : ℕ} (hn : 0 < n) (j : Fin n) :
    |Real.sin ((n : ℝ) * rootAngle n j)| = 1 := by
  have hsq : Real.sin ((n : ℝ) * rootAngle n j) ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq ((n : ℝ) * rootAngle n j)
    rw [cos_mul_rootAngle hn j] at h
    simpa using h
  rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]

lemma sin_rootAngle_pos {n : ℕ} (hn : 0 < n) (j : Fin n) :
    0 < Real.sin (rootAngle n j) :=
  Real.sin_pos_of_pos_of_lt_pi (rootAngle_mem hn j).1 (rootAngle_mem hn j).2

lemma chebyshev_natDegree (n : ℕ) : (T ℝ (n : ℤ)).natDegree = n := by
  simp only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]

lemma chebyshev_root {n : ℕ} (hn : 0 < n) (j : Fin n) :
    (T ℝ (n : ℤ)).eval ((chebyshevNodes n hn).point j) = 0 := by
  rw [chebyshevNodes_point, T_real_cos]
  simpa only [Int.cast_natCast] using cos_mul_rootAngle hn j

/-- Derivative formula with no quotient by sin θ. -/
lemma chebyshev_derivative_mul_sin (n : ℕ) (θ : ℝ) :
    (T ℝ (n : ℤ)).derivative.eval (Real.cos θ) * Real.sin θ =
      (n : ℝ) * Real.sin ((n : ℝ) * θ) := by
  rw [T_derivative_eq_U, Polynomial.eval_mul, Polynomial.eval_intCast,
    Int.cast_natCast, mul_assoc]
  have hu := U_real_cos θ ((n : ℤ) - 1)
  simpa only [Int.cast_sub, Int.cast_one, sub_add_cancel, Int.cast_natCast] using
    congrArg (fun z : ℝ => (n : ℝ) * z) hu

lemma abs_derivative_mul_sin_rootAngle {n : ℕ} (hn : 0 < n) (j : Fin n) :
    |(T ℝ (n : ℤ)).derivative.eval (Real.cos (rootAngle n j))| *
        Real.sin (rootAngle n j) = (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := congrArg abs (chebyshev_derivative_mul_sin n (rootAngle n j))
  simpa only [abs_mul, abs_of_pos (sin_rootAngle_pos hn j), abs_of_pos hnR,
    abs_sin_mul_rootAngle hn j, mul_one] using h

/-- Multiplicative cardinal formula, valid even AT interpolation nodes. -/
lemma cardinal_weighted_identity {n : ℕ} (hn : 0 < n) (j : Fin n) (θ : ℝ) :
    |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| * (n : ℝ) *
      |Real.cos θ - Real.cos (rootAngle n j)| =
        Real.sin (rootAngle n j) * |Real.cos ((n : ℝ) * θ)| := by
  have h := nodal_polynomial_cardinal_identity hn (chebyshevNodes n hn)
    (T ℝ (n : ℤ)) (chebyshev_natDegree n) (chebyshev_root hn) j (Real.cos θ)
  have habs := congrArg abs h
  simp only [T_real_cos, Int.cast_natCast, chebyshevNodes_point, abs_mul] at habs
  calc
    |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| * (n : ℝ) *
        |Real.cos θ - Real.cos (rootAngle n j)| =
      |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| *
        (|(T ℝ (n : ℤ)).derivative.eval (Real.cos (rootAngle n j))| *
          Real.sin (rootAngle n j)) * |Real.cos θ - Real.cos (rootAngle n j)| := by
      rw [abs_derivative_mul_sin_rootAngle hn j]
    _ = Real.sin (rootAngle n j) *
        (|Real.cos θ - Real.cos (rootAngle n j)| *
          |(T ℝ (n : ℤ)).derivative.eval (Real.cos (rootAngle n j))| *
            |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)|) := by ring
    _ = Real.sin (rootAngle n j) * |Real.cos ((n : ℝ) * θ)| := by rw [← habs]

/-- The only possible zero angular denominator is treated separately. -/
lemma cardinal_angular_weighted {n : ℕ} (hn : 0 < n) (j : Fin n) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| *
      ((n : ℝ) * |θ - rootAngle n j|) ≤ Real.pi * |Real.cos ((n : ℝ) * θ)| := by
  by_cases heq : θ = rootAngle n j
  · subst θ
    simp only [sub_self, abs_zero, mul_zero, cos_mul_rootAngle hn j, le_refl]
  · have hcosne : Real.cos θ - Real.cos (rootAngle n j) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hc
      exact heq (Real.injOn_cos hθ (rootAngle_mem_closed hn j) hc)
    have hD : 0 < |Real.cos θ - Real.cos (rootAngle n j)| := abs_pos.mpr hcosne
    have hgeom := sin_mul_distance_le_pi_mul_cos_distance θ (rootAngle n j)
      hθ (rootAngle_mem_closed hn j)
    have hscaled :
        (|lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| *
          ((n : ℝ) * |θ - rootAngle n j|)) *
          |Real.cos θ - Real.cos (rootAngle n j)| ≤
        (Real.pi * |Real.cos ((n : ℝ) * θ)|) *
          |Real.cos θ - Real.cos (rootAngle n j)| := by
      calc
        _ = (|lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| * (n : ℝ) *
            |Real.cos θ - Real.cos (rootAngle n j)|) * |θ - rootAngle n j| := by ring
        _ = (Real.sin (rootAngle n j) * |Real.cos ((n : ℝ) * θ)|) *
            |θ - rootAngle n j| := by rw [cardinal_weighted_identity hn j θ]
        _ = (Real.sin (rootAngle n j) * |θ - rootAngle n j|) *
            |Real.cos ((n : ℝ) * θ)| := by ring
        _ ≤ (Real.pi * |Real.cos θ - Real.cos (rootAngle n j)|) *
            |Real.cos ((n : ℝ) * θ)| :=
          mul_le_mul_of_nonneg_right hgeom (abs_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_right hscaled hD

lemma cos_bound_by_root_distance {n : ℕ} (hn : 0 < n) (j : Fin n) (θ : ℝ) :
    |Real.cos ((n : ℝ) * θ)| ≤ (n : ℝ) * |θ - rootAngle n j| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.abs_cos_sub_cos_le ((n : ℝ) * θ) ((n : ℝ) * rootAngle n j)
  rw [cos_mul_rootAngle hn j, sub_zero, ← mul_sub, abs_mul, abs_of_pos hnR] at h
  exact h

/-- A uniform bound is needed for the nearest node, including exact node hits. -/
lemma cardinal_le_pi_add_one {n : ℕ} (hn : 0 < n) (j : Fin n) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| ≤ Real.pi + 1 := by
  by_cases heq : θ = rootAngle n j
  · subst θ
    change |lagrangeFundamental (chebyshevNodes n hn) j
      ((chebyshevNodes n hn).point j)| ≤ Real.pi + 1
    rw [lagrangeFundamental_self, abs_one]
    linarith [Real.pi_pos]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hδ : 0 < |θ - rootAngle n j| := abs_pos.mpr (sub_ne_zero.mpr heq)
    have hW : 0 < (n : ℝ) * |θ - rootAngle n j| := mul_pos hnR hδ
    have h := (cardinal_angular_weighted hn j θ hθ).trans
      (mul_le_mul_of_nonneg_left (cos_bound_by_root_distance hn j θ) Real.pi_pos.le)
    have hpi : |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| ≤ Real.pi :=
      le_of_mul_le_mul_right h hW
    linarith

/-- Away from its own node, a cardinal function decays inversely with angle. -/
lemma cardinal_le_inverse_distance {n : ℕ} (hn : 0 < n) (j : Fin n) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) (hne : θ ≠ rootAngle n j) :
    |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)| ≤
      Real.pi / ((n : ℝ) * |θ - rootAngle n j|) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 < |θ - rootAngle n j| := abs_pos.mpr (sub_ne_zero.mpr hne)
  apply (le_div_iff₀ (mul_pos hnR hδ)).2
  have h := (cardinal_angular_weighted hn j θ hθ).trans
    (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ((n : ℝ) * θ)) Real.pi_pos.le)
  simpa only [mul_one] using h

/-- Nearest-node selection plus the triangle inequality gives the separation
bound directly. No rounding function or endpoint exception is needed. -/
lemma nearest_index_separation {n : ℕ} (hn : 0 < n) (θ : ℝ) (p : Fin n)
    (hp : ∀ j, |θ - rootAngle n p| ≤ |θ - rootAngle n j|) (j : Fin n) :
    |(j.val : ℝ) - (p.val : ℝ)| * (Real.pi / (n : ℝ)) ≤
      2 * |θ - rootAngle n j| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htri := abs_sub_le (rootAngle n j) θ (rootAngle n p)
  rw [rootAngle_sub, abs_mul, abs_of_pos (div_pos Real.pi_pos hnR),
    abs_sub_comm (rootAngle n j) θ] at htri
  linarith [hp j]

/-- A fully finite bound for the actual Lebesgue function of the competitor. -/
theorem chebyshev_lebesgue_cos_le {n : ℕ} (hn : 0 < n) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    lebesgueFunction (chebyshevNodes n hn) (Real.cos θ) ≤
      Real.pi + 1 + 4 * harmonicReal n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨p, _hp, hpmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin n)) (fun j => |θ - rootAngle n j|) hnonempty
  have hp : ∀ j, |θ - rootAngle n p| ≤ |θ - rootAngle n j| :=
    fun j => hpmin j (Finset.mem_univ j)
  apply sum_le_of_index_distance p
    (fun j => |lagrangeFundamental (chebyshevNodes n hn) j (Real.cos θ)|)
    (Real.pi + 1) (cardinal_le_pi_add_one hn p θ hθ)
  intro j hjp
  have hidx : 0 < |(j.val : ℝ) - (p.val : ℝ)| := by
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    intro heq
    apply hjp
    apply Fin.ext
    exact_mod_cast heq
  have hsep := nearest_index_separation hn θ p hp j
  have hδ : 0 < |θ - rootAngle n j| := by
    have hpos : 0 < |(j.val : ℝ) - (p.val : ℝ)| * (Real.pi / (n : ℝ)) :=
      mul_pos hidx (div_pos Real.pi_pos hnR)
    linarith
  have hjθ : θ ≠ rootAngle n j := sub_ne_zero.mp (abs_pos.mp hδ)
  apply (cardinal_le_inverse_distance hn j θ hθ hjθ).trans
  apply (div_le_div_iff₀ (mul_pos hnR hδ) hidx).2
  have h := mul_le_mul_of_nonneg_left hsep hnR.le
  have hcancel : (n : ℝ) *
      (|(j.val : ℝ) - (p.val : ℝ)| * (Real.pi / (n : ℝ))) =
        Real.pi * |(j.val : ℝ) - (p.val : ℝ)| := by
    field_simp [hnR.ne'] <;> ring
  rw [hcancel] at h
  nlinarith

/-- From cosine coordinates back to the full interval, including its endpoints. -/
theorem chebyshev_lebesgue_le {n : ℕ} (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    lebesgueFunction (chebyshevNodes n hn) x ≤ Real.pi + 1 + 4 * harmonicReal n := by
  have h := chebyshev_lebesgue_cos_le hn (Real.arccos x)
    ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩
  rwa [Real.cos_arccos hx.1 hx.2] at h

/-- The maximum is attained; the pointwise estimate bounds that maximum. -/
theorem chebyshev_lebesgueOn_le {n : ℕ} (hn : 0 < n) :
    lebesgueOn (chebyshevNodes n hn) (-1) 1 ≤ Real.pi + 1 + 4 * harmonicReal n := by
  obtain ⟨x, hx, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge (chebyshevNodes n hn)
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  rw [heq]
  exact chebyshev_lebesgue_le hn x hx

/-- A single explicit constant, independent of n and of the original nodes. -/
def logConstant : ℝ := 4 + (Real.pi + 5) / Real.log 2

lemma logConstant_pos : 0 < logConstant := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold logConstant
  positivity

/-- A concrete competitor with a logarithmic global amplification bound. -/
theorem chebyshev_lebesgueOn_log {n : ℕ} (hn : 2 ≤ n) :
    lebesgueOn (chebyshevNodes n (by omega)) (-1) 1 ≤
      logConstant * Real.log (n : ℝ) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmon : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hnR
  have hquot : 0 ≤ (Real.pi + 5) / Real.log 2 := by positivity [Real.pi_pos]
  have habsorb := mul_le_mul_of_nonneg_left hmon hquot
  rw [div_mul_cancel₀ _ hlog.ne'] at habsorb
  calc
    lebesgueOn (chebyshevNodes n (by omega)) (-1) 1 ≤
        Real.pi + 1 + 4 * harmonicReal n := chebyshev_lebesgueOn_le (n := n) (by omega)
    _ ≤ Real.pi + 5 + 4 * Real.log (n : ℝ) := by linarith [harmonicReal_le n]
    _ ≤ logConstant * Real.log (n : ℝ) := by
      unfold logConstant
      nlinarith

end
end JSPFreeNodes.Logarithmic
