module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory

open Filter Topology

theorem countVol_le_selfInter : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  intro k _ X _ p D d a L A m hAHS hX hL hA hd ha hm
  have hmul : Tendsto (fun j : ℕ => a * j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j ha) tendsto_id
  have h1 := ((hAHS.tendsto_of_triv hX hL hA).comp hmul).div_const ((d : ℝ) * ((D : ℝ) + 1))
  have h2 := ENNReal.tendsto_ofReal h1
  refine (limsup_le_limsup ?_).trans_eq h2.limsup_eq
  filter_upwards [hmul.eventually (hAHS.of_triv hX hL hA).1, eventually_ge_atTop 1] with j hfin hj
  have hx : 0 ≤ Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hN : (0 : ℝ) < ((a * j : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.mul_pos ha hj)
  have hd' : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hlog : logCard (m (a * j)) ≤ ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) := by
    rw [← logCard_coe, hfin.cast_ncard_eq]
    exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (hm j hj)))
  have hden : (d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((d : ℝ) * ((a * j : ℕ) : ℝ) ^ (D + 1)) := by
    rw [ENNReal.ofReal_mul hd'.le, ENNReal.ofReal_pow hN.le, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  calc _ ≤ (D.factorial : ℝ≥0∞) * ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) /
        ((d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1)) := by gcongr
    _ = _ := by
      rw [hden, ← ENNReal.ofReal_natCast (D.factorial), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [Function.comp]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp

end GlobalTheory
