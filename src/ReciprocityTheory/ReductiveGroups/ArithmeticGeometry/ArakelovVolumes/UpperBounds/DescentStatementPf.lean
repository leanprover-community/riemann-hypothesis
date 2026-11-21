import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FunKerSt

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def KerDimStatement : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] (sg : K →+* ℂ) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    letI : Algebra K ℂ := sg.toAlgebra
    ∀ (Wc : Submodule ℂ (ℂ ⊗[K] V)) (FF : Set (Module.Dual ℂ (ℂ ⊗[K] V))),
    (∀ c ∈ FF, ∃ K' : IntermediateField K ℂ, FiniteDimensional K K' ∧ DefinedOver c K') →
    (∀ c ∈ FF, Wc ≤ LinearMap.ker c) →
    (∀ x ∈ baseSpan ℂ (⊤ : Submodule K V), x ∉ Wc → ∃ c ∈ FF, c x ≠ 0) →
    (∀ c ∈ FF, ∀ K₂ : IntermediateField K ℂ, FiniteDimensional K K₂ → IsGalois K K₂ →
      DefinedOver c K₂ → ∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ descend K₂ Wc,
        c (inclT K₂ V (galAct σ x)) = 0) →
    Submodule.span ℂ ((fun v => (1 : ℂ) ⊗ₜ[K] v) '' {v : V | (1 : ℂ) ⊗ₜ[K] v ∈ Wc}) = Wc ∧
      Module.finrank K (Submodule.span K {v : V | (1 : ℂ) ⊗ₜ[K] v ∈ Wc}) = Module.finrank ℂ Wc

def DescentStatement : Prop :=
  ∀ (F F' V : Type) [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
    (ι : Type) [Fintype ι] (v : ι → V),
    (LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i)) ∧
    (∀ x : V, x ∈ Submodule.span F (Set.range v) ↔
      (1 : F') ⊗ₜ[F] x ∈ Submodule.span F' (Set.range fun i => (1 : F') ⊗ₜ[F] v i)) ∧
    Module.finrank F (Submodule.span F (Set.range v)) =
      Module.finrank F' (Submodule.span F' (Set.range fun i => (1 : F') ⊗ₜ[F] v i))

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

open scoped TensorProduct
open Module

variable {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]

theorem indep_iff {ι : Type} (v : ι → V) :
    LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i) := by
  constructor
  · intro hv
    exact Module.Flat.linearIndependent_one_tmul hv
  · intro h
    have h' : LinearIndependent F (fun i => (1 : F') ⊗ₜ[F] v i) :=
      h.restrict_scalars' F
    exact LinearIndependent.of_comp (TensorProduct.mk F F' V 1) h'

end ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
