module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatementStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicCompleteStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvrStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5

theorem exists_valuationSubring_isInt_comap :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type)
      [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
      ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧ ∀ x, x ∈ B ↔ IsInt (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ hC j
  have hvaluation : ∃ v : Valuation Ωl NNReal,
      (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) ∧ v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      hirr.maximalIdeal_eq
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hmax]
      exact GlobalTheory.T.unramified_integers_adic_complete p
    have := hC.alg
    obtain ⟨v, hv⟩ :=
      GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ωl hC.inj
    have : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hle : v (p : Ωl) ≤ 1 := (hv _).2 (by
      simpa [IsInt] using GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ))
    refine ⟨v, hv, lt_of_le_of_ne hle ?_⟩
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hint : IsInt (p := p) ((p : Ωl)⁻¹) := (hv _).1 hi
    exact GlobalTheory.K5.Basic.not_cong_one_zero hC 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  obtain ⟨v, hv, hp1⟩ := hvaluation
  let w : Valuation Ω NNReal := v.comap j
  refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
      ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
    show v (j ((p : ℕ) : Ω)) < 1
    rw [map_natCast]
    exact hp1
  · rw [Valuation.mem_valuationSubring_iff]
    exact hv (j x)

end GlobalTheory.K5
