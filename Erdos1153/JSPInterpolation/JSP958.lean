import Erdos1153.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JSP-000958 / Erdős 1153

This file is an attributed adapter to Ethan Yang's existing proof:
https://github.com/ethn-y/erdos-1153-lean
commit 03bd3e064c0b95e8e7d335fa0f3e3de0713ca777.

The upstream proof, not a new proof authored in this response, supplies the
entire mathematical theorem. Its CI was inspected in the preceding work; it is not a CI run for these new modules. These additional adapter
declarations have NOT been compiled in this session.
-/

namespace JSPInterpolation

/-- The original uniform epsilon/eventual proposition. -/
theorem jsp_000958 : Erdos1153.Target :=
  Erdos1153.erdos1153_main

/-- The same result with the actual interval maximum written explicitly.
The threshold N is chosen BEFORE n and BEFORE the node family. -/
theorem jsp_000958_maximum :
    ∀ a b : ℝ,
      -1 ≤ a → a < b → b ≤ 1 →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 2 ≤ N ∧
          ∀ n : ℕ, N ≤ n → ∀ nodes : Erdos1153.NodeFamily n,
            (2 / Real.pi - ε) * Real.log (n : ℝ) <
              Erdos1153.lebesgueOn nodes a b := by
  intro a b ha hab hb ε hε
  obtain ⟨N, hN, hproof⟩ := jsp_000958 a b ha hab hb ε hε
  refine ⟨N, hN, ?_⟩
  intro n hn nodes
  exact (Erdos1153.lt_lebesgueOn_iff nodes hab.le).mpr
    (hproof n hn nodes)

end JSPInterpolation

