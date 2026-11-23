module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem fib_card {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (z : H) :
    Fintype.card G = Fintype.card H * (Finset.univ.filter (fun y => f y = z)).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hc : ∀ b ∈ (Finset.univ : Finset H),
      (Finset.univ.filter (fun a => f a = b)).card = (Finset.univ.filter (fun y => f y = z)).card :=
    fun b _ => MonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf z)
  rw [Finset.card_univ, Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact h

theorem UpperTheory.card_fiber_reduction_eq_totient :
    ∀ (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N], ¬ l ∣ N → ∀ z : (ZMod (l ^ (m + n)))ˣ, (Finset.univ.filter (fun y => redTop l n m N y = z)).card = Nat.totient (N * N) := by
  intro l _ n m N _ hN z
  have hl : l.Prime := Fact.out
  have hdvd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (topM l n m (N * N)) :=
    ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  have key := fib_card (ZMod.unitsMap hdvd) (ZMod.unitsMap_surjective hdvd) z
  have hred : ∀ y, redTop l n m N y = ZMod.unitsMap hdvd y := fun y => rfl
  simp only [hred]
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at key
  have hcop : (l ^ (m + n)).Coprime (N * N) := by
    have h1 : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hN
    exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h1 h1)
  have htot : (topM l n m (N * N)).totient = (l ^ (m + n)).totient * (N * N).totient :=
    Nat.totient_mul hcop
  rw [htot] at key
  have hpos : 0 < (l ^ (m + n)).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
  exact (Nat.eq_of_mul_eq_mul_left hpos key).symm
