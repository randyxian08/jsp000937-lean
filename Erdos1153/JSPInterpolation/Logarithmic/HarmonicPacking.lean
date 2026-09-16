import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A finite harmonic packing estimate

A distinguished index contributes at most K.  Every other index at integer
index-distance r contributes at most 2/r.  Map the left and right indices
separately, injectively, into {1,...,n}; the total is at most K + 4 H_n.

This module has no assumptions about interpolation or its desired bound.
-/

namespace JSPFreeNodes.Logarithmic
noncomputable section
open scoped BigOperators

/-- The real harmonic sum, indexed by positive integers (no 1/0 term). -/
def harmonicReal (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹

lemma harmonicReal_eq (n : ℕ) : harmonicReal n = (harmonic n : ℝ) := by
  simp only [harmonicReal, harmonic_eq_sum_Icc, Rat.cast_sum,
    Rat.cast_inv, Rat.cast_natCast]

lemma harmonicReal_le (n : ℕ) : harmonicReal n ≤ 1 + Real.log (n : ℝ) := by
  rw [harmonicReal_eq]
  exact harmonic_le_one_add_log n

/-- The harmonic estimate needs only index-distance bounds, not an ordered
or positive function f.  Its distinguished-index bound is supplied explicitly. -/
lemma sum_le_of_index_distance {n : ℕ} (p : Fin n) (f : Fin n → ℝ) (K : ℝ)
    (hp : f p ≤ K)
    (hfar : ∀ j : Fin n, j ≠ p →
      f j ≤ 2 / |(j.val : ℝ) - (p.val : ℝ)|) :
    (∑ j : Fin n, f j) ≤ K + 4 * harmonicReal n := by
  classical
  let L : Finset (Fin n) := Finset.univ.filter (fun j => j < p)
  let R : Finset (Fin n) := Finset.univ.filter (fun j => p < j)
  have hL (j : Fin n) (hj : j ∈ L) : j.val < p.val :=
    (Finset.mem_filter.mp hj).2
  have hR (j : Fin n) (hj : j ∈ R) : p.val < j.val :=
    (Finset.mem_filter.mp hj).2
  have hcover : (Finset.univ : Finset (Fin n)) = insert p (L ∪ R) := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      rcases lt_trichotomy j p with hj | hj | hj
      · exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inl
            (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))))
      · exact Finset.mem_insert.mpr (Or.inl hj)
      · exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr
            (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))))
    · intro _
      exact Finset.mem_univ j
  have hpnot : p ∉ L ∪ R := by simp [L, R]
  have hdisj : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro j hjL hjR
    have h₁ := hL j hjL
    have h₂ := hR j hjR
    omega
  have hleft : (∑ j ∈ L, f j) ≤ 2 * harmonicReal n := by
    have hinj : Set.InjOn (fun j : Fin n => p.val - j.val) L := by
      intro i hi j hj hij
      -- Expose the natural-number equality before omega; do not leave a lambda application.
      change p.val - i.val = p.val - j.val at hij
      apply Fin.ext
      have hi' := hL i hi
      have hj' := hL j hj
      omega
    have hsub : L.image (fun j => p.val - j.val) ⊆ Finset.Icc 1 n := by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      have hj' := hL j hj
      have hp' := p.isLt
      simp only [Finset.mem_Icc]
      omega
    calc
      (∑ j ∈ L, f j) ≤ ∑ j ∈ L, 2 * (((p.val - j.val : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := hL j hj
        have hjne : j ≠ p := by intro heq; subst j; omega
        have hjle : (j.val : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hj'.le
        have habs : |(j.val : ℝ) - (p.val : ℝ)| =
            ((p.val - j.val : ℕ) : ℝ) := by
          rw [abs_of_nonpos (sub_nonpos.mpr hjle), Nat.cast_sub hj'.le]
          ring
        simpa only [habs, div_eq_mul_inv] using hfar j hjne
      _ = ∑ r ∈ L.image (fun j => p.val - j.val), 2 * (r : ℝ)⁻¹ := by
        rw [Finset.sum_image hinj]
      _ ≤ ∑ r ∈ Finset.Icc 1 n, 2 * (r : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro r _hr _hnot
        positivity
      _ = 2 * harmonicReal n := by rw [harmonicReal, Finset.mul_sum]
  have hright : (∑ j ∈ R, f j) ≤ 2 * harmonicReal n := by
    have hinj : Set.InjOn (fun j : Fin n => j.val - p.val) R := by
      intro i hi j hj hij
      -- Expose the natural-number equality before omega; do not leave a lambda application.
      change i.val - p.val = j.val - p.val at hij
      apply Fin.ext
      have hi' := hR i hi
      have hj' := hR j hj
      omega
    have hsub : R.image (fun j => j.val - p.val) ⊆ Finset.Icc 1 n := by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      have hj' := hR j hj
      have hjn := j.isLt
      simp only [Finset.mem_Icc]
      omega
    calc
      (∑ j ∈ R, f j) ≤ ∑ j ∈ R, 2 * (((j.val - p.val : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := hR j hj
        have hjne : j ≠ p := by intro heq; subst j; omega
        have hjle : (p.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hj'.le
        have habs : |(j.val : ℝ) - (p.val : ℝ)| =
            ((j.val - p.val : ℕ) : ℝ) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hjle), Nat.cast_sub hj'.le]
        simpa only [habs, div_eq_mul_inv] using hfar j hjne
      _ = ∑ r ∈ R.image (fun j => j.val - p.val), 2 * (r : ℝ)⁻¹ := by
        rw [Finset.sum_image hinj]
      _ ≤ ∑ r ∈ Finset.Icc 1 n, 2 * (r : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro r _hr _hnot
        positivity
      _ = 2 * harmonicReal n := by rw [harmonicReal, Finset.mul_sum]
  calc
    (∑ j : Fin n, f j) = f p + ((∑ j ∈ L, f j) + ∑ j ∈ R, f j) := by
      rw [hcover, Finset.sum_insert hpnot, Finset.sum_union hdisj]
    _ ≤ K + 4 * harmonicReal n := by linarith

end
end JSPFreeNodes.Logarithmic
