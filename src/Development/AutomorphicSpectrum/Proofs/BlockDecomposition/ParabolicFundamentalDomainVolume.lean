module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem ae_exists_smul_mem_image_prod :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ᵐ p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)), ∃ γ : Γ, γ • p ∈ (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕
  rw [(GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι).measurableEmbedding.ae_map_iff]
  have hcov : ∀ᵐ z ∂(ν.prod μ₁), ∃ γ₁ : Γ₁, γ₁ • z.2 ∈ 𝓕₁ :=
    Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers
  filter_upwards [hcov] with z hz
  obtain ⟨m, u⟩ := z
  obtain ⟨γ₁, hγ₁⟩ := hz
  obtain ⟨δ, hδ, -⟩ := hD (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) *
    MulAut.conjNormal (ι (π (ι γ₁))) m)
  have hδΓ : ((δ : π.ker) : P) ∈ Γ := Subgroup.mem_subgroupOf.mp δ.2
  refine ⟨⟨((δ : π.ker) : P) * ι γ₁, Γ.mul_mem hδΓ (hΓ γ₁ γ₁.2)⟩,
    ⟨(δ • (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) * MulAut.conjNormal (ι (π (ι γ₁))) m),
      γ₁ • u), ⟨hδ, hγ₁⟩, ?_⟩⟩
  simp only [GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply, Subgroup.smul_def, smul_eq_mul,
    Subgroup.coe_mul]
  rw [mul_assoc (((δ : π.ker) : P)) (ι (γ₁ : G₁)), GlobalTheory.CompanionTheory.SplitExtLat.mul_split ι π hπι (ι γ₁) m u,
    hπι, Subgroup.coe_mul, mul_assoc]

end GlobalTheory.CompanionTheory.SplitExtLat
