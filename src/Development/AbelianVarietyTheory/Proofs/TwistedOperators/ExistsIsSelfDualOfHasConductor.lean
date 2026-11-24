module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}

theorem isSelfDual_iff_vol (h : HasConductor ψ c) (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1 := by
  have := t2Space k
  have hcl : IsClosed (𝒪[k] : Set k) := (isCompact_int k).isClosed
  have hclo : IsClopen (𝒪[k] : Set k) := ⟨hcl, isOpen_int k⟩
  set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf
  have hfSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · have hlc := (LocallyConstant.charFn ℂ hclo).isLocallyConstant
      exact hlc
    · exact HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]
  have hf0 : f 0 = 1 := by simp [f]
  have hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal := measureReal_def ν _
  constructor
  · rintro ⟨-, hsd⟩
    have e := (fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)
    rw [hf0, mul_one] at e
    rw [← hvol]
    exact_mod_cast e
  · intro hC
    refine ⟨inferInstance, fun g hg => ?_⟩
    rw [fourier_inversion ν h hg, hvol, hC]
    simp

theorem exists_isSelfDual_of_hasConductor (h : HasConductor ψ c) : ∃ ν : Measure k, IsSelfDual ψ ν := by
  obtain ⟨ν₀, hH, h1⟩ := exists_isUnitVol k
  have hn : 0 < nabs k c := nabs_pos k c
  set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have : (Real.sqrt (nabs k c))⁻¹ = 0 := congrArg Subtype.val h0
    have hs : 0 < Real.sqrt (nabs k c) := Real.sqrt_pos.2 hn
    exact (inv_pos.2 hs).ne' this
  have : (a • ν₀).IsAddHaarMeasure := .nnreal_smul ν₀ ha0
  refine ⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩
  have hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹ := by
    rw [smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
    rfl
  rw [hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']

theorem isUnitVol_iff_isSelfDual (h : HasConductor ψ 1) (ν : Measure k) : IsUnitVol ν ↔ IsSelfDual ψ ν := by
  constructor
  · intro hν
    haveI := hν.1
    exact isSelfDual_of_isUnitVol ν h hν
  · intro hsd
    haveI : ν.IsAddHaarMeasure := hsd.1
    have e := (isSelfDual_iff_vol h ν).1 hsd
    rw [nabs_one, mul_one] at e
    have hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal := ENNReal.toReal_nonneg
    have e1 : (ν (𝒪[k] : Set k)).toReal = 1 := by nlinarith
    exact ⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩

theorem selfDual_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1), (∃ ν : Measure k, IsSelfDual ψ ν) ∧ (HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν ↔ IsSelfDual ψ ν) ∧ ∀ (c : kˣ) (ν : Measure k), HasConductor ψ c → ν.IsAddHaarMeasure → (IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1) := by
  intro k _ _ _ _ _ _ ψ hψ h1
  refine ⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    exact exists_isSelfDual_of_hasConductor hc
  · exact isSelfDual_iff_vol hc ν

end GlobalTheory.SplitWeil
