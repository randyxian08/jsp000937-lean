import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Elementary estimates used below. In particular no interpolation bound
is imported, postulated, or represented by an additional hypothesis. -/

namespace JSPFreeNodes.Logarithmic
noncomputable section

/-- A chord-line estimate, with the absolute value and its range checked. -/
lemma angle_distance_le_sine (θ φ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi) :
    |θ - φ| ≤ Real.pi * |Real.sin ((θ - φ) / 2)| := by
  have hd : |(θ - φ) / 2| ≤ Real.pi / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]
  have hc := Real.mul_abs_le_abs_sin hd
  have h := mul_le_mul_of_nonneg_left hc Real.pi_pos.le
  have hcancel : Real.pi * (2 / Real.pi * |(θ - φ) / 2|) =
      2 * |(θ - φ) / 2| := by
    field_simp [Real.pi_pos.ne'] <;> ring
  rw [hcancel] at h
  calc
    |θ - φ| = 2 * |(θ - φ) / 2| := by
      rw [abs_div]
      norm_num <;> ring
    _ ≤ Real.pi * |Real.sin ((θ - φ) / 2)| := h

/-- The weighted cosine denominator dominates the angular distance. This
form avoids division by sin((θ+φ)/2), including near the endpoints. -/
lemma sin_mul_distance_le_pi_mul_cos_distance (θ φ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi) :
    Real.sin φ * |θ - φ| ≤ Real.pi * |Real.cos θ - Real.cos φ| := by
  have hs : 0 ≤ Real.sin ((θ + φ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, hφ.1])
      (by linarith [hθ.2, hφ.2])
  have hsinθ : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hmid : Real.sin φ ≤ 2 * Real.sin ((θ + φ) / 2) := by
    calc
      Real.sin φ ≤ Real.sin θ + Real.sin φ := by linarith
      _ = 2 * Real.sin ((θ + φ) / 2) * Real.cos ((θ - φ) / 2) :=
        Real.sin_add_sin θ φ
      _ ≤ 2 * Real.sin ((θ + φ) / 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.cos_le_one ((θ - φ) / 2)) (by positivity :
            0 ≤ 2 * Real.sin ((θ + φ) / 2))
  have hcos : |Real.cos θ - Real.cos φ| =
      2 * Real.sin ((θ + φ) / 2) * |Real.sin ((θ - φ) / 2)| := by
    rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_of_nonneg hs]
    norm_num
  calc
    Real.sin φ * |θ - φ| ≤
        (2 * Real.sin ((θ + φ) / 2)) * |θ - φ| :=
      mul_le_mul_of_nonneg_right hmid (abs_nonneg _)
    _ ≤ (2 * Real.sin ((θ + φ) / 2)) *
        (Real.pi * |Real.sin ((θ - φ) / 2)|) :=
      mul_le_mul_of_nonneg_left (angle_distance_le_sine θ φ hθ hφ)
        (by positivity : 0 ≤ 2 * Real.sin ((θ + φ) / 2))
    _ = Real.pi * |Real.cos θ - Real.cos φ| := by rw [hcos]; ring

end
end JSPFreeNodes.Logarithmic
