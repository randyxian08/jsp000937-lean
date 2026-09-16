import Erdos1153.JSPInterpolation.AllGaps
import Erdos1153.JSPInterpolation.Logarithmic.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The complete JSP-000937 public target

The public statement is unchanged from v2/v2.1: arbitrary distinct nodes,
all n+1 intervals (including both exterior intervals), classification and
one uniform logarithmic bound for all n >= 2. The one-node classification
is included in Target937Classification; log(1)=0 is not used as a bound.

This file finally supplies a proof body for BOTH conjuncts. The newly
supplied source must still pass the pinned compiler and axiom audit.
-/

namespace JSPFreeNodes
open Erdos1153
noncomputable section

/-- A finite, non-asymptotic form of the bound for arbitrary free nodes. -/
theorem allMinPeak_le_explicit_harmonic {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ Real.pi + 1 + 4 * Logarithmic.harmonicReal (d + 2) := by
  let competitor : NodeFamily (d + 2) :=
    Logarithmic.chebyshevNodes (d + 2) (by omega)
  calc
    allMinPeak nodes ≤ amplification competitor :=
      allMinPeak_le_any_amplification nodes competitor
    _ ≤ Real.pi + 1 + 4 * Logarithmic.harmonicReal (d + 2) :=
      Logarithmic.chebyshev_lebesgueOn_le (n := d + 2) (by omega)

/-- The same explicit real constant works for every cardinality and every
free node family. No endpoint or ordering hypothesis is added. -/
theorem allMinPeak_le_explicit_log {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ Logarithmic.logConstant * Real.log ((d + 2 : ℕ) : ℝ) := by
  let competitor : NodeFamily (d + 2) :=
    Logarithmic.chebyshevNodes (d + 2) (by omega)
  calc
    allMinPeak nodes ≤ amplification competitor :=
      allMinPeak_le_any_amplification nodes competitor
    _ = lebesgueOn (Logarithmic.chebyshevNodes (d + 2) (by omega)) (-1) 1 := rfl
    _ ≤ Logarithmic.logConstant * Real.log ((d + 2 : ℕ) : ℝ) :=
      Logarithmic.chebyshev_lebesgueOn_log (n := d + 2) (by omega)

/-- A strict variant, for formulations of the source question using `<`.
The constant is enlarged once, independently of the nodes and n. -/
theorem allMinPeak_lt_explicit_log {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes <
      (Logarithmic.logConstant + 1) * Real.log ((d + 2 : ℕ) : ℝ) := by
  have hn : (1 : ℝ) < ((d + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < d + 2 by omega)
  have hlog : 0 < Real.log ((d + 2 : ℕ) : ℝ) := Real.log_pos hn
  have h := allMinPeak_le_explicit_log nodes
  nlinarith

/-- The formerly missing public logarithmic-growth request, now with a
proof body that constructs and estimates an actual competing node family. -/
theorem jsp_000937_logarithmic : Target937Logarithmic := by
  refine ⟨Logarithmic.logConstant, Logarithmic.logConstant_pos, ?_⟩
  intro d nodes
  exact allMinPeak_le_explicit_log nodes

/-- Original complete 937 target: maximizer classification AND logarithmic
upper bound. This is not an alias for the classification alone. -/
theorem jsp_000937 : Target937 :=
  ⟨jsp_000937_classification, jsp_000937_logarithmic⟩

end
end JSPFreeNodes
