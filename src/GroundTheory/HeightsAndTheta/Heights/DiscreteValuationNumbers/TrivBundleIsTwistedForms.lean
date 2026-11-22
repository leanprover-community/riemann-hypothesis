module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w u₁ u₂

section Coordinates

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

end Coordinates

section Flags

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Flags

section ProjBundle

variable {K : Type*} [Fintype K]

variable {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section PolyNum

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def monoList {N : ℕ} (mono : Fin N →₀ ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun l => List.replicate (mono l) l

variable {F : Type*} [Field F]

end PolyNum

section Pairs

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

variable {Ω : Type*} [Field Ω] [Algebra O Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Pairs

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

variable {o}

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end DVR

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
