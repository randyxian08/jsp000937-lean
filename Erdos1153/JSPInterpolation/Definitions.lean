import Erdos1153.GapPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Independent public statements for JSP-000936 and JSP-000937

This module imports interpolation definitions, NOT the de Boor--Pinkus
comparison theorem or any proof of either prize problem.

A competitor is the original `Erdos1153.NodeFamily`: an injective family of
points in [-1,1], with neither extreme node prescribed.  Sorting identifies
consecutive gaps without requiring the input enumeration to be increasing.
-/

namespace JSPFreeNodes
open Erdos1153
noncomputable section

/-! ## Literal objectives and an unrestricted competitor type -/

/-- The actual maximum of the Lebesgue function on the AMBIENT interval. -/
def amplification {n : ℕ} (nodes : NodeFamily n) : ℝ :=
  lebesgueOn nodes (-1) 1

/-- The actual minimum of the finitely many adjacent-gap maxima.
The type `Fin (d+1)` is nonempty, including the two-node case `d=0`. -/
def orderedMinPeak {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  sInf (Set.range (fun i : Fin (d + 1) => gapHeight nodes i))

/-- For an arbitrarily enumerated node family, use its actual increasing
ordering to identify consecutive gaps. -/
def minPeak {d : ℕ} (nodes : NodeFamily (d + 2)) : ℝ :=
  orderedMinPeak nodes.sorted

/-- Global minimization over ALL distinct nodes in [-1,1]. -/
def IsMinimizer {n : ℕ} (nodes : NodeFamily n) : Prop :=
  ∀ other : NodeFamily n, amplification nodes ≤ amplification other

/-- Auxiliary INTERNAL-gap maximization over all node families.
This is NOT the original JSP-000937 objective. -/
def IsInternalMaximizer {d : ℕ} (nodes : NodeFamily (d + 2)) : Prop :=
  ∀ other : NodeFamily (d + 2), minPeak other ≤ minPeak nodes


/-- A normalized equioscillating REFERENCE configuration. This predicate is
required only of the existential reference, never of an arbitrary competitor. -/
def IsNormalizedEquioscillating {d : ℕ} (reference : NodeFamily (d + 2)) : Prop :=
  reference.sorted.point 0 = -1 ∧
  reference.sorted.point (Fin.last (d + 1)) = 1 ∧
  ∀ i j : Fin (d + 1),
    gapHeight reference.sorted i = gapHeight reference.sorted j

/-- A positive affine copy of the reference, with the affine map taking the
whole unit interval into itself. No endpoints of `nodes` are prescribed. -/
def AdmissibleAffineCopy {d : ℕ}
    (reference nodes : NodeFamily (d + 2)) : Prop :=
  ∃ c scale : ℝ, 0 < scale ∧ |c| + scale ≤ 1 ∧
    ∀ i, nodes.sorted.point i = c + scale * reference.sorted.point i

/-- Complete minimax statement for all positive cardinalities.

For one node every placement is optimal. For every n=d+2>=2 there is a
normalized equioscillating reference, attaining the global minimum over
ALL node families. Its admissible affine copies satisfying the two exterior
endpoint tests are EXACTLY all global minimizers. -/
def Target936 : Prop :=
  (∀ nodes : NodeFamily 1, IsMinimizer nodes) ∧
  ∀ d : ℕ, ∃ reference : NodeFamily (d + 2),
    IsNormalizedEquioscillating reference ∧
    IsMinimizer reference ∧
    ∀ nodes : NodeFamily (d + 2),
      amplification reference ≤ amplification nodes ∧
      (IsMinimizer nodes ↔
        AdmissibleAffineCopy reference nodes ∧
        lebesgueFunction nodes (-1) ≤ amplification reference ∧
        lebesgueFunction nodes 1 ≤ amplification reference)

/-- Auxiliary INTERNAL-gap maximin statement. Both exterior intervals
are omitted here; the original objective and target are stated below. -/
def TargetInternalMaximin : Prop :=
  ∀ d : ℕ, ∃ reference : NodeFamily (d + 2),
    IsNormalizedEquioscillating reference ∧
    IsInternalMaximizer reference ∧
    ∀ nodes : NodeFamily (d + 2),
      minPeak nodes ≤ minPeak reference ∧
      (IsInternalMaximizer nodes ↔ AdmissibleAffineCopy reference nodes)

/-! ## The original JSP-000937 objective INCLUDES the two exterior intervals -/

/-- The n+1 actual interval maxima, indexed without artificial interpolation
nodes. `none` is [-1,x_first], `some none` is [x_last,1], and
`some (some i)` is the i-th internal adjacent-node interval.
The added endpoints are interval boundaries, NOT additional interpolation
nodes; the Lagrange function still uses exactly d+2 original nodes. -/
def augmentedGapHeight {d : ℕ} (nodes : NodeFamily (d + 2)) :
    Option (Option (Fin (d + 1))) → ℝ
  | none => lebesgueOn nodes (-1) (nodes.sorted.point 0)
  | some none => lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1
  | some (some i) => gapHeight nodes.sorted i

/-- Literal minimum over ALL n+1 intervals, including both exterior intervals. -/
def allMinPeak {d : ℕ} (nodes : NodeFamily (d + 2)) : ℝ :=
  sInf (Set.range (augmentedGapHeight nodes))

/-- Original JSP-000937 maximization, over unrestricted node families. -/
def IsFullMaximizer {d : ℕ} (nodes : NodeFamily (d + 2)) : Prop :=
  ∀ other : NodeFamily (d + 2), allMinPeak other ≤ allMinPeak nodes

/-- The all-gap objective for one interpolation node has two exterior intervals. -/
def oneNodeAllMinPeak (nodes : NodeFamily 1) : ℝ :=
  min (lebesgueOn nodes (-1) (nodes.point 0))
    (lebesgueOn nodes (nodes.point 0) 1)

def IsOneNodeFullMaximizer (nodes : NodeFamily 1) : Prop :=
  ∀ other : NodeFamily 1, oneNodeAllMinPeak other ≤ oneNodeAllMinPeak nodes

/-- Exact free-node maximizer classification for the ORIGINAL all-gap objective.
The normalized reference describes the optimal SHAPE, but is not asserted
to maximize allMinPeak. A separately constructed compressed array attains
the value, and both exterior endpoint tests are necessary and sufficient. -/
def Target937Classification : Prop :=
  (∀ nodes : NodeFamily 1, IsOneNodeFullMaximizer nodes) ∧
  ∀ d : ℕ, ∃ reference : NodeFamily (d + 2),
    IsNormalizedEquioscillating reference ∧
    (∃ maximizer : NodeFamily (d + 2),
      IsFullMaximizer maximizer ∧
      allMinPeak maximizer = amplification reference) ∧
    ∀ nodes : NodeFamily (d + 2),
      allMinPeak nodes ≤ amplification reference ∧
      (IsFullMaximizer nodes ↔
        AdmissibleAffineCopy reference nodes ∧
        amplification reference ≤ lebesgueFunction nodes (-1) ∧
        amplification reference ≤ lebesgueFunction nodes 1)

/-- The other request in Erdős 1130: a uniform logarithmic upper bound.
This is deliberately separate from classification, so proving only the
classification cannot be mislabeled a proof of the entire original question. -/
def Target937Logarithmic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ nodes : NodeFamily (d + 2),
    allMinPeak nodes ≤ C * Real.log ((d + 2 : ℕ) : ℝ)

/-- Full original JSP-000937 task, including BOTH requests. -/
def Target937 : Prop := Target937Classification ∧ Target937Logarithmic

end
end JSPFreeNodes
