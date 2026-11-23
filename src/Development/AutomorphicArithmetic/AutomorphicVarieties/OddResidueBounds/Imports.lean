module

public import Formalism.GaloisCohomology.Statement
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FnOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.SelCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrSel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.gen :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧ (g : ℝ) ≤ 8 * l * Module.finrank ℚ E * Real.log ((l : ℝ) * N) := by
  intro E Ω _ _ _ _ _ N hN hE l hl D e
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨hdeg, hζ, hemb⟩ := fnOne E Ω l
  obtain ⟨f, hf⟩ := unrInj E Ω l D e
  obtain ⟨f', hf'⟩ := unrSel (Fn E Ω l 1) Ω l hζ
  obtain ⟨hfin, hcard⟩ := selCard (Fn E Ω l 1) l
  have hH := logH (Fn E Ω l 1) (l * N) (by nlinarith) (hemb N hN hE)
  haveI := Finite.of_injective _ (hf'.comp hf)
  obtain ⟨k, hk, hc⟩ := lenOfCard l (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]))
  have h1 := (Nat.card_le_card_of_injective _ (hf'.comp hf)).trans hcard
  rw [hc] at h1
  have hn : Module.finrank ℚ (Fn E Ω l 1) ≤ l * Module.finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ E (Fn E Ω l 1), mul_comm]
    exact Nat.mul_le_mul_right _ ((Nat.le_of_dvd (by omega) hdeg).trans (by omega))
  refine ⟨k, hk.le, ?_⟩
  have hh : (0 : ℝ) < classNumber (Fn E Ω l 1) := by exact_mod_cast classNumber_pos _
  generalize Module.finrank ℚ (Fn E Ω l 1) = m at *
  generalize classNumber (Fn E Ω l 1) = h at *
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (2 * m) * h := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (by positivity) hh.ne', Real.log_pow, Real.log_pow] at h3
  push_cast at h3 hH
  have ha : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl'
  have hb : Real.log l ≤ Real.log ((l : ℝ) * N) := Real.log_le_log (by positivity) (by nlinarith)
  have h2' := Real.log_two_gt_d9
  have hn' : (m : ℝ) ≤ l * Module.finrank ℚ E := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left hb hm
  have h5 : (k : ℝ) * (5 / 8) ≤ k * Real.log l := mul_le_mul_of_nonneg_left (by linarith) hk0
  have h6 := mul_le_mul_of_nonneg_right hn' (show 0 ≤ Real.log ((l : ℝ) * N) by linarith)
  nlinarith
