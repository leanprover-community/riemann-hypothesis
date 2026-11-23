module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleIsCoboundary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatDescent

def restrictR {R D A E : Type} [CommRing R] [CommRing D] [CommRing A] [CommRing E]
    [Algebra R D] [Algebra R A] [Algebra R E] [Algebra D A] [Algebra D E]
    (hA : ∀ r, algebraMap D A (algebraMap R D r) = algebraMap R A r)
    (hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r)
    (f : A →ₐ[D] E) : A →ₐ[R] E :=
  ⟨f.toRingHom, fun r => by
    show f (algebraMap R A r) = algebraMap R E r
    rw [← hA r, ← hE r]; exact f.commutes _⟩

theorem cocycle_descends : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ (c : ∀ (E : Type) [CommRing E] [Algebra R E], (D' →ₐ[R] E) → (D' →ₐ[R] E) → E), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (α β : D' →ₐ[R] E) (ρ : E →ₐ[R] E'), α.comp ψ = β.comp ψ → c E' (ρ.comp α) (ρ.comp β) = ρ (c E α β)) → (∀ (E : Type) [CommRing E] [Algebra R E] (f₁ f₂ f₃ : D' →ₐ[R] E), f₁.comp ψ = f₂.comp ψ → f₂.comp ψ = f₃.comp ψ → c E f₁ f₃ = c E f₁ f₂ + c E f₂ f₃) → ∃ a : D', ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → c E α β = β a - α a := by
  intro R _ D D' _ _ _ _ ψ hψ c hnat hcoc
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  letI instRT : Algebra R (D' ⊗[D] D') :=
    ((algebraMap D (D' ⊗[D] D')).comp (algebraMap R D)).toAlgebra
  have h' : ∀ r, algebraMap D D' (algebraMap R D r) = algebraMap R D' r := fun r => ψ.commutes r
  have hT : ∀ r, algebraMap D (D' ⊗[D] D') (algebraMap R D r) = algebraMap R (D' ⊗[D] D') r :=
    fun _ => rfl
  let i₁ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeLeft
  let i₂ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeRight
  have h12 : i₁.comp ψ = i₂.comp ψ := by
    ext d
    exact ((Algebra.TensorProduct.includeLeft (R := D) (S := D) (A := D') (B := D')).commutes d).trans
      ((Algebra.TensorProduct.includeRight (R := D) (A := D') (B := D')).commutes d).symm
  obtain ⟨a, ha⟩ := GlobalTheory.AmitsurCohomologyH1.cocycle_is_coboundary D D' (c (D' ⊗[D] D') i₁ i₂) (by
    intro E _ _ f₁ f₂ f₃
    letI : Algebra R E := ((algebraMap D E).comp (algebraMap R D)).toAlgebra
    have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun _ => rfl
    have key : ∀ f g : D' →ₐ[D] E,
        Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) =
          c E (restrictR h' hE f) (restrictR h' hE g) := by
      intro f g
      let ρ : D' ⊗[D] D' →ₐ[R] E :=
        restrictR hT hE (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _))
      have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
      have e1 : ρ.comp i₁ = restrictR h' hE f := by
        ext x; simp [ρ, i₁, restrictR]
      have e2 : ρ.comp i₂ = restrictR h' hE g := by
        ext x; simp [ρ, i₂, restrictR]
      rw [e1, e2] at hn
      exact hn.symm
    have hc : ∀ f g : D' →ₐ[D] E, (restrictR h' hE f).comp ψ = (restrictR h' hE g).comp ψ := by
      intro f g; ext d
      exact (f.commutes d).trans (g.commutes d).symm
    rw [key, key, key]
    exact hcoc E _ _ _ (hc _ _) (hc _ _))
  refine ⟨a, ?_⟩
  intro E _ _ α β hαβ
  letI : Algebra D E := ((α.comp ψ : D →ₐ[R] E) : D →+* E).toAlgebra
  let α' : D' →ₐ[D] E := ⟨α.toRingHom, fun _ => rfl⟩
  let β' : D' →ₐ[D] E := ⟨β.toRingHom, fun d => by
    show β (ψ d) = α (ψ d)
    exact (DFunLike.congr_fun hαβ d).symm⟩
  have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun r => by
    show α (ψ _) = _
    rw [ψ.commutes, α.commutes]
  let ρ : D' ⊗[D] D' →ₐ[R] E :=
    restrictR hT hE (Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _))
  have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
  have e1 : ρ.comp i₁ = α := by
    ext x; simp [ρ, i₁, α', restrictR]
  have e2 : ρ.comp i₂ = β := by
    ext x; simp [ρ, i₂, β', restrictR]
  rw [e1, e2] at hn
  rw [hn]
  show Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) = _
  rw [ha]
  simp [α', β']

end GlobalTheory.FlatDescent
