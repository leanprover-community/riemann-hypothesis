module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult

noncomputable section

namespace GlobalTheory.SplitTorusZero

open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

variable {D : D7} {V : HSp D}

theorem rat_mem_GQ (g : GF V) : rat V g ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨g, rfl⟩

theorem zeroClause_of_conj (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ g : GF V)
    (h : ZeroClause μ f (rat V (g * γ * g⁻¹))) : ZeroClause μ f (rat V γ) := by
  have hg := rat_mem_GQ g
  have e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ) := by
    ext δ
    simp only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨rat V g * k, mul_mem hg hk, by group⟩
  intro 𝓕 h𝓕
  have := h 𝓕 h𝓕
  unfold HasClassInt classKernel at *
  rw [e] at this
  exact this

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_of_quot {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) (hi : Integrable (descend (GQ V) φ) (autMeasure V μ)) :
    IntegrableOn φ 𝓕 μ ∧ ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)
    rw [hφ.lift_descend] at this
    exact memLp_one_iff_integrable.1 this
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

end GlobalTheory.SplitTorusZero
