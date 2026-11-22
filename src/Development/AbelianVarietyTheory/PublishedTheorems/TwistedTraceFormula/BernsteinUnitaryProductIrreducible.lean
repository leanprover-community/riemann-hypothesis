module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def BernsteinUnitaryProductIrreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ →
    IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
    (prod₂ π₁ π₂).IsIrreducible

namespace BernsteinUnitaryProductIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end BernsteinUnitaryProductIrreducible

end GlobalTheory.Published
