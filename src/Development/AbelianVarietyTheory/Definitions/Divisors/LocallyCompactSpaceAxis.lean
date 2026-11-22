module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import GroundTheory.GlobalFields.Adele.IntegersLattice

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure IsHt {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (h : G → ℝ) : Prop where
  pos : ∀ g, 0 < h g
  cont : Continuous h
  one : ∀ k ∈ K, h k = 1
  iw : ∀ g, ∃ k ∈ K, ∀ x, h (g * x) = h g * h (k * x)

instance countable_inf {G : Type} [Group G] (Γ H : Subgroup G) [Countable Γ] : Countable (Γ ⊓ H : Subgroup G) :=
  (Subgroup.inclusion_injective inf_le_left).countable

structure SemiLat {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N M Λ : Subgroup G) (ν : Measure N)
    (π : Measure M) (𝓝 : Set N) (𝓜 : Set M) : Prop where
  closedN : IsClosed (N : Set G)
  closedM : IsClosed (M : Set G)
  norm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N
  disj : ∀ g ∈ N, g ∈ M → g = 1
  dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m
  haarN : ν.IsHaarMeasure
  haarM : π.IsHaarMeasure
  domN : IsFundamentalDomain (Λ.subgroupOf N) 𝓝 ν
  domM : IsFundamentalDomain (Λ.subgroupOf M) 𝓜 π
  finN : ν 𝓝 ≠ ⊤
  finM : π 𝓜 ≠ ⊤
  count : Countable Λ := by infer_instance
  topGrp : IsTopologicalGroup G := by infer_instance
  borel : BorelSpace G := by infer_instance

namespace Inhab

open GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem semiLat_ne_zero {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {N M Λ : Subgroup G} {ν : Measure N} {π : Measure M} {𝓝 : Set N} {𝓜 : Set M}
    (H : SemiLat N M Λ ν π 𝓝 𝓜) : ν 𝓝 ≠ 0 := by
  haveI := H.haarN
  haveI := H.count
  haveI := H.topGrp
  haveI := H.borel
  haveI : Countable (Λ.subgroupOf N) := Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, x.2⟩ : Λ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (·.1) h))
  exact H.domN.measure_ne_zero (NeZero.ne ν)

end Inhab

end GlobalTheory.ResLine

end
