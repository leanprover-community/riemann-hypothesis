module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogDisc
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassC
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logH :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 2 ≤ N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → Real.log (classNumber E) ≤ 3 * Module.finrank ℚ E * Real.log N := by
  intro E _ _ N hN hE
  obtain ⟨hd, hn⟩ := UpperTheory.V.Odd.logDisc E N (by omega) hE
  have hc := KStar.IdealCounting.log_classNumber_le E
  have hd1 : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have hd2 : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E := by
    have h : (((discr E).natAbs : ℕ) : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E := by exact_mod_cast hd
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (Module.finrank ℚ E : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := Nat.cast_nonneg _
  generalize Module.finrank ℚ E = n at *
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hD0 : 0 ≤ Real.log |(discr E : ℝ)| := Real.log_nonneg hd1
  have hD : Real.log |(discr E : ℝ)| ≤ n * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hd2
  have hnL : (n : ℝ) * Real.log N ≤ N * (N - 1) := mul_le_mul hn' hL1 hL0 (by linarith)
  have h2 : Real.log (1 + Real.log |(discr E : ℝ)| / 2) ≤ 2 * Real.log N := by
    have e : 2 * Real.log N = Real.log ((N : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn0
  have h4 := mul_nonneg hn0 hL0
  nlinarith
