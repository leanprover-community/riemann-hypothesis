module

public import Formalism.EllipticTorsion.Statement
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public section

universe u

namespace Formalism.ELL

def ChangeIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K),
    IntegralModel W → IntegralModel (C • W) → W.Δ ≠ 0 → ‖(C • W).Δ‖ = ‖W.Δ‖ →
      ‖(C.u : K)‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1

end Formalism.ELL
