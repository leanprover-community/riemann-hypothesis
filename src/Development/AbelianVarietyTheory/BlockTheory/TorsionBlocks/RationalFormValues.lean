module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCoefExt {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (ι : K →+* K')
    {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) (c' : VV K' lam →ₛₗ[σ'] W) : Prop :=
  ∀ (v : VV K lam) (v' : VV K' lam), (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) → c' v' = c₀ v

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

end
