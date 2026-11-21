import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZeroMemSphSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarishChandraReproducingFunctionGLinfinity

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_toUnits_Kinf : Continuous (Unitary.toUnits : Kinf E a → GL (Fin a) (Cinf E)) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩

theorem continuous_translate (φ : Sm E a) (g : GA E a) :
    Continuous fun y : GL (Fin a) (Cinf E) => φ.1 (g * infGL E a y) := by
  have h1 : ContinuousOn (chart φ.1 g) (invSet E a) := (φ.2 g).continuousOn
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val := by
    show Continuous fun y : GL (Fin a) (Cinf E) => (y : Matrix (Fin a) (Fin a) (Cinf E))
    exact Units.continuous_val
  have e : (fun y : GL (Fin a) (Cinf E) => φ.1 (g * infGL E a y)) = fun y => chart φ.1 g (toL y.val) :=
    funext fun y => (chart_val φ.1 g y).symm
  rw [e]
  exact h1.comp_continuous h2 fun y => val_mem_invSet y



theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite →
    ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧
      HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g :=
  GlobalTheory.T.exists_harishChandra_reproducing_function_GLinfinity

end GlobalTheory.HCAlphaGL

end
