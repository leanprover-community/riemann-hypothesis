module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerTheta_eq_neg_genBernoulli :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) (k : ℕ), 2 ≤ N → ev ℚ χ (thetaEl k π) = -genB k (dirOf π χ) / k := by
  intro Ω _ _ N _ Γ _ π χ k hN
  haveI : Fact (1 < N) := ⟨hN⟩
  have hsum : ∀ f : ZMod N → Ω, (∀ x, ¬ IsUnit x → f x = 0) →
      ∑ x, f x = ∑ u : (ZMod N)ˣ, f u := by
    intro f hf
    symm
    rw [show ∑ u : (ZMod N)ˣ, f u = ∑ x ∈ Finset.univ.map ⟨Units.val, Units.val_injective⟩, f x by
      rw [Finset.sum_map]; rfl]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply hf
    rintro ⟨u, rfl⟩
    exact hx (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)
  have h1 : ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k a) =
      ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k (a : ZMod N).val) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨_, h2⟩ := Finset.mem_Icc.1 ha
    rcases h2.lt_or_eq with h | rfl
    · rw [ZMod.val_cast_of_lt h]
    · rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul]

  simp only [thetaEl, sumEl, map_neg, map_sum, ev_single, genB, Ek]
  rw [h1, b_sumicc (fun x : ZMod N => dirOf π χ x * algebraMap ℚ Ω (bcoef N k x.val)),
    hsum _ (fun x hx => by simp [MulChar.map_nonunit _ hx])]
  simp only [dirOf_unit]
  rw [neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_div₀, map_natCast]
  ring
