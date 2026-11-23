module

public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem vw_lw_arith : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  intro K _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w a b ha hb
    exact Formalism.DivisionValues.ValuationRepresentative.vw_mul w a b ha hb
  · intro w m d hd hmd
    obtain ⟨k, rfl⟩ := hmd
    have hm0 : m ≠ 0 := by rintro rfl; simp at hd
    have hk0 : k ≠ 0 := by rintro rfl; simp at hd
    have hnn : ∀ n : ℕ, 0 ≤ Formalism.DivisionValues.vw w (n : K) := by
      intro n
      have h := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w ((n : ℕ) : 𝓞 K)
      simpa using h
    refine ⟨hnn m, ?_⟩
    rw [Nat.cast_mul, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (by exact_mod_cast hm0) (by exact_mod_cast hk0)]
    linarith [hnn k]
  · intro d hd
    have hf := FractionalIdeal.finite_factors (K := K)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (d : K))
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset ?_
    intro w hw
    exact hw
  · intro d hd s
    exact Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s d hd.ne'

end GlobalTheory
