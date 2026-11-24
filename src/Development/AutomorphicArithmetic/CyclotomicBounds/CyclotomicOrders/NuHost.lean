module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuRecord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace UpperTheory.KStar

theorem nu_eq_nuL {D : D7} (i : D.ntw.Tw) : (BlochKatoReduction.Gen.nu D.ntw i : ℝ) = TwistedPlaces.nuL D (D.ntw.l i) := by
  unfold TwistedPlaces.nuL
  rw [dif_pos (D.ntw.lPrime i).out]
  rfl

def nuBudget (D : D7) : ℝ := Real.log (D.host.QS : ℝ) + Real.log ((D.R.t * D.R.r : ℕ) : ℝ)

theorem nuL_eq_zero_of_g (D : D7) (l : ℕ) (h : l ∈ TwistedPlaces.gset D) (_h2 : l ≠ 2) : TwistedPlaces.nuL D l = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, l = D.host.g k := by
    rcases Finset.mem_insert.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, Finset.mem_singleton.1 h⟩
  haveI := Fact.mk (D.host.g_prime k)
  unfold TwistedPlaces.nuL
  rw [dif_pos (D.host.g_prime k), Nat.cast_eq_zero]
  exact UpperTheory.Mu.nu_eq_zero_of_split D.host D.nd.Om _ (D.nd.g_split k)

theorem nuL_eq_zero_of_qd (D : D7) (l : ℕ) (h : l = D.host.q ∨ l = D.host.d) : TwistedPlaces.nuL D l = 0 := by
  unfold TwistedPlaces.nuL
  split_ifs with hl
  · haveI := Fact.mk hl
    rw [Nat.cast_eq_zero]
    exact UpperTheory.Mu.nu_eq_zero_of_qd D.host D.nd.Om l h
  · rfl

theorem sum_nuL_le (D : D7) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, TwistedPlaces.nuL D l * Real.log l ≤ nuBudget D :=
  UpperTheory.Mu.sum_nu_le D.host D.nd.Om (TwistedPlaces.nuL D) (fun _ hl => dif_pos hl.out) S hS

theorem nuBudget_le (D : D7) : nuBudget D ≤ 2 * Real.log D.R.n + Real.log D.R.t + Real.log D.R.r :=
  UpperTheory.Mu.budget_le D.host

end UpperTheory.KStar
