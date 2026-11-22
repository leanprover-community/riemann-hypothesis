module

public import Mathlib
public import Formalism.FormalGroupLog.Statement

@[expose] public section

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def deuring {K : Type u} [CommRing K] (a : K) : WeierstrassCurve K :=
  ⟨a, 0, 1, 0, 0⟩

def IntegralModel {K : Type u} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def DeuringInv : Prop :=
  ∀ (K : Type u) [CommRing K] (a : K),
    (deuring a).Δ = a ^ 3 - 27 ∧ (deuring a).c₄ = a * (a ^ 3 - 24)

def ModelDeuring : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K],
    ‖(3 : K)‖ = 1 → ∀ j : K, ‖j‖ ≤ 1 →
      ∃ a : K, ‖a‖ ≤ 1 ∧
        (deuring a).c₄ ^ 3 = j * (deuring a).Δ ∧ ‖(deuring a).Δ‖ = 1

section Cong

variable {K : Type u} [NormedField K] [CharZero K] {σ : Type}

end Cong

end Formalism.ELL
