import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5390

-- The function on the eight bits, checked over all 256 inputs.
theorem bits (C : PEqualNP.CircuitLowerBounds.Circuit)
    (h : C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit)) :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      PEqualNP.MetaComplexity.circuitFun 8 C ![b0, b1, b2, b3, b4, b5, b6, b7] =
        decide (∃ e ∈ ([(0, 3), (1, 3), (4, 6), (4, 7), (5, 6)] : List (Fin 8 × Fin 8)),
          (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) e.1 = true ∧
          (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) e.2 = true) := by
  subst h
  decide

end PEqualNP.Outside.L_meta_5390

theorem PEqualNP.Outside.L_meta_5390 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 8 C ∧ C.size = 12 ∧
  (∀ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 C x = decide (∃ e ∈ ([(0, 3), (1, 3), (4, 6), (4, 7), (5, 6)] : List (Fin 8 × Fin 8)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 3), (1, 3), (4, 6), (4, 7), (5, 6)] : List (Fin 8 × Fin 8)), PEqualNP.Core.ReadTwiceAt 8 C (C.output - 8) e.1 e.2 ↔ e ∈ ([(0, 3), (4, 6), (4, 7), (5, 6)] : List (Fin 8 × Fin 8))) := by
  intro C h
  have hb := PEqualNP.Outside.L_meta_5390.bits C h
  subst h
  refine ⟨by decide, by decide, ?_, by decide⟩
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact hb _ _ _ _ _ _ _ _
