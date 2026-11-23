module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.minkRam :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K ≠ 1 → ∃ p : ℕ, p.Prime ∧ ¬ UnramAt K p := by
  intro K _ _ hK
  have h1 : 1 < Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  have h2 := NumberField.abs_discr_gt_two h1
  set D := differentIdeal ℤ (𝓞 K) with hD
  have hnorm : D.absNorm = (NumberField.discr K).natAbs :=
    NumberField.absNorm_differentIdeal K (𝓞 K)
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hnorm
    have h3 : ((NumberField.discr K).natAbs : ℤ) = |NumberField.discr K| := Int.natCast_natAbs _
    rw [← hnorm] at h3
    omega
  obtain ⟨P, hPmax, hDP⟩ := Ideal.exists_le_maximal D hDtop
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hDP
    exact differentIdeal_ne_bot hDP
  haveI : NeZero P := ⟨hPne⟩
  refine ⟨Ideal.absNorm (Ideal.under ℤ P), Nat.absNorm_under_prime P, fun hun => ?_⟩
  have hram := hun P hPmax.isPrime (Int.absNorm_under_mem P)
  rw [Ideal.ramificationIdx_eq_one_iff] at hram
  exact (dvd_differentIdeal_iff.mp (Ideal.dvd_iff_le.mpr hDP)) hram
