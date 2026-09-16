import Erdos1153.Interpolation
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The nodal-polynomial cardinal identity

For any degree-n polynomial vanishing at the n interpolation nodes, factor
out one simple linear factor. Its degree-(n-1) quotient has only one nonzero
interpolation value. Exact interpolation then gives the desired identity.
No formula for a Lagrange basis is assumed.
-/

namespace JSPFreeNodes.Logarithmic
open Erdos1153 Polynomial
open scoped BigOperators
noncomputable section

lemma nodal_polynomial_cardinal_identity {n : ℕ} (hn : 0 < n)
    (nodes : NodeFamily n) (p : ℝ[X]) (hpdeg : p.natDegree = n)
    (hroot : ∀ j, p.eval (nodes.point j) = 0)
    (k : Fin n) (x : ℝ) :
    p.eval x = (x - nodes.point k) *
      p.derivative.eval (nodes.point k) * lagrangeFundamental nodes k x := by
  classical
  have hpne : p ≠ 0 := by
    intro hp
    rw [hp, Polynomial.natDegree_zero] at hpdeg
    omega
  have hdiv : Polynomial.X - Polynomial.C (nodes.point k) ∣ p :=
    Polynomial.dvd_iff_isRoot.mpr (hroot k)
  obtain ⟨q, hq⟩ := hdiv
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact hpne hq
  have hdegree := congrArg Polynomial.natDegree hq
  rw [hpdeg, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hqne,
    Polynomial.natDegree_X_sub_C] at hdegree
  have hqnat : q.natDegree < n := by omega
  have hqdeg : q.degree < (n : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hqnat)
  have hqroot (j : Fin n) (hjk : j ≠ k) : q.eval (nodes.point j) = 0 := by
    have heval := congrArg (fun r : ℝ[X] => r.eval (nodes.point j)) hq
    simp only [hroot j, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left
      (sub_ne_zero.mpr (nodes.injective.ne hjk))
  have hder : p.derivative.eval (nodes.point k) = q.eval (nodes.point k) := by
    rw [hq, Polynomial.derivative_mul]
    simp
  have hqeval : q.eval x =
      q.eval (nodes.point k) * lagrangeFundamental nodes k x := by
    calc
      q.eval x = ∑ j : Fin n,
          q.eval (nodes.point j) * lagrangeFundamental nodes j x :=
        eval_lagrangeExpansion nodes q hqdeg x
      _ = q.eval (nodes.point k) * lagrangeFundamental nodes k x := by
        apply Finset.sum_eq_single k
        · intro j _hj hjk
          rw [hqroot j hjk, zero_mul]
        · intro hk
          exact False.elim (hk (Finset.mem_univ k))
  calc
    p.eval x = (x - nodes.point k) * q.eval x := by
      rw [hq, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
    _ = (x - nodes.point k) * p.derivative.eval (nodes.point k) *
        lagrangeFundamental nodes k x := by
      rw [hqeval, ← hder]
      ring

end
end JSPFreeNodes.Logarithmic
