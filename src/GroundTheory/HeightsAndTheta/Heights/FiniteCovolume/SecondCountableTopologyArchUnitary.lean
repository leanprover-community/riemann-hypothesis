module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

universe u

section Topology

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

instance secondCountableTopology_GL_complex : SecondCountableTopology (GL ι ℂ) := by
  have : SecondCountableTopology (Matrix ι ι ℂ) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))
  have : SecondCountableTopology (Matrix ι ι ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

instance secondCountableTopology_archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    SecondCountableTopology (archUnitary h v) := by
  have : SecondCountableTopology (InfinitePlace E → GL ι ℂ) := inferInstance
  exact TopologicalSpace.Subtype.secondCountableTopology _

end Topology

section Groups

variable (G : Type*) [Group G]

def UnfoldOrbit.Statement [MeasurableSpace G] [MeasurableMul G] : Prop :=
  ∀ (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ₀ : Subgroup G) [Countable Γ], Γ₀ ≤ Γ →
    ∀ FD FD₀ : Set G, IsFundamentalDomain Γ FD μ → IsFundamentalDomain Γ₀ FD₀ μ →
    ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ₀, ∀ g, φ (γ * g) = φ g) →
    ∫⁻ g in FD, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ g in FD₀, φ g ∂μ

def DiscreteFundamentalDomain.Statement [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] : Prop :=
  ∀ (μ : Measure G) (Γ : Subgroup G), DiscreteTopology Γ →
    ∃ FD : Set G, MeasurableSet FD ∧ IsFundamentalDomain Γ FD μ

end Groups

section Numbers

variable (E : Type*) [Field E] [NumberField E]

def IdealClassesFinite.Statement : Prop :=
  ∃ T : Set (AddSubgroup E), T.Finite ∧ ∀ I : AddSubgroup E, I.FG → I ≠ ⊥ →
    (∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I) →
    ∃ J ∈ T, ∃ c : E, c ≠ 0 ∧ I = J.map (AddMonoidHom.mulLeft c)

def IntegralFamilyBound.Statement : Prop :=
  ∃ r : ℝ, ∃ a : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
    ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r

end Numbers

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def MajorantExists.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  Nonempty (Majorant h v)

def WittPartner.Statement (h : HermitianForm F E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 → ∃ w₀ : W, h.toSesq x₀ w₀ = 1 ∧ h.toSesq w₀ w₀ = 0

def VectorOrbitsFinite.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (VV : Set W), IsDIntegral h D La → VV ⊆ La →
    (∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) → (∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV) →
    (∃ C : ℕ, ∀ x ∈ VV, lineIndex E La x ≤ C) →
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x

def ArchLatticeDiscrete.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La → DiscreteTopology (archLatticeGroup h v La)

variable (F E)

def CovolumeFiniteBelow (N : ℕ) : Prop :=
  ∀ (W' : Type u) [AddCommGroup W'] [Module E W'] [FiniteDimensional E W']
    (h' : HermitianForm F E W') (n : ℕ) (v' : Basis (Fin n) E W'),
    finrank E W' < N → ArithmeticCovolumeFinite.Statement h' v'

def LatticeOrbitsFiniteBelow (N : ℕ) : Prop :=
  ∀ (W' : Type u) [AddCommGroup W'] [Module E W'] [FiniteDimensional E W']
    (h' : HermitianForm F E W'), finrank E W' < N → LatticeOrbitsFinite.Statement h'

end Spaces

section Inhabitants

open GaussianPlane

abbrev C2 : Type := Multiplicative (ZMod 2)

instance : MeasurableSpace C2 := ⊤

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
