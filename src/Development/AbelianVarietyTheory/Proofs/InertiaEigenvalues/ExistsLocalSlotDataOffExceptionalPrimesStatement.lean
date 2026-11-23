module

public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.exists_localPositionData_off_exceptional_primes : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  first | exact @GlobalTheory.LocalPositionData.position_data_exist | exact GlobalTheory.LocalPositionData.position_data_exist | (intros; apply GlobalTheory.LocalPositionData.position_data_exist <;> assumption)
