module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Mathlib.Data.Int.WithZero
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

open IsDedekindDomain IsLocalRing

theorem exists_realValuation_of_discreteValuationSubring {Ω : Type} [Field Ω]
    (V : ValuationSubring Ω) [IsDiscreteValuationRing V] :
    ∃ ν : Valuation Ω ℝ≥0, (∀ x : V, ν (x : Ω) ≤ 1) ∧ ∀ x ∈ maximalIdeal V, ν (x : Ω) < 1 := by
  have hne : maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let v : HeightOneSpectrum V := ⟨maximalIdeal V, inferInstance, hne⟩
  let hmono := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num))
  refine ⟨Valuation.map { WithZeroMulInt.toNNReal (e := 2) (by norm_num) with
    monotone' := hmono.monotone } (v.valuation Ω),
    fun x => ?_, fun x hx => ?_⟩
  · have h := v.valuation_le_one (K := Ω) x
    have := hmono.monotone h
    simpa using this
  · have h := (v.valuation_lt_one_iff_mem (K := Ω) x).mpr hx
    have := hmono h
    simpa using this

theorem isIntegral_of_forall_realValuation_le_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  intro K Ω _ _ _ _ hfg A hA t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType K Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType A Ω := .of_comp K A Ω
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hic : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure A Ω).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := A) W
    (fun r => hW ((integralClosure A Ω).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  obtain ⟨ν, hν1, hνm⟩ := exists_realValuation_of_discreteValuationSubring V
  have hle : ν t ≤ 1 := ht ν fun a ha => hν1 ⟨a, h2 ⟨a, ha⟩⟩
  have hn3 : t⁻¹ ∈ V.nonunits := h3 _ rfl
  have htV : t⁻¹ ∈ V :=
    (V.valuation_le_one_iff _).mp (le_of_lt ((V.mem_nonunits_iff).mp hn3))
  have hm : (⟨t⁻¹, htV⟩ : V) ∈ maximalIdeal V :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨t⁻¹, htV⟩)).mp hn3
  have hlt : ν t⁻¹ < 1 := hνm _ hm
  have h1' : ν (t * t⁻¹) = 1 := by rw [mul_inv_cancel₀ ht0, map_one]
  rw [map_mul] at h1'
  have : ν t * ν t⁻¹ < 1 := lt_of_le_of_lt (mul_le_of_le_one_left zero_le hle) hlt
  exact absurd h1' this.ne

end GlobalTheory.DegVal
