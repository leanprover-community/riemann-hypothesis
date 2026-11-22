module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.IndefR.Heis

section Law

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[ext] structure HeisG (B : M →ₗ[R] M →ₗ[R] R) where

  w : M

  t : R

namespace HeisG

variable {B : M →ₗ[R] M →ₗ[R] R} [Invertible (2 : R)]

end HeisG

end Law

section Rat

variable {E : Type*} [Field E] [NumberField E] (c : E →+* E)

variable {c}

end Rat

section Ad

variable {𝔸 WA : Type*} [CommRing 𝔸] [AddCommGroup WA] [Module 𝔸 WA]

variable [Invertible (2 : 𝔸)] (ψ : AddChar 𝔸 ℂ) (B : WA →ₗ[𝔸] WA →ₗ[𝔸] 𝔸)

end Ad

section D7

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def FinCovol (V W : HSp D) : Prop :=
  (∃ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V W) 𝓕 μ) ∧
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ → μ 𝓕 < ⊤

end D7

end Formalism.IndefR.Heis

end
