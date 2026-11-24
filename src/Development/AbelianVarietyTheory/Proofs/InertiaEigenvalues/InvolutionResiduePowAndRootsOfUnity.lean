module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial IsLocalRing

namespace GlobalTheory.UnitLemma.InvolRes

theorem residue_pow_and_roots : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ),
    Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) →
    (∃ x, residue S (τ x) ≠ residue S x) →
    (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  intro S _ _ _ M hM τ hττ hne
  let e : S ≃+* S := RingEquiv.ofRingHom τ τ (RingHom.ext hττ) (RingHom.ext hττ)
  let s := ResidueField.mapEquiv e
  have hs : ∀ x, s (residue S x) = residue S (τ x) := fun x => rfl
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  haveI := hp
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField S) p⟩
  obtain ⟨-, hsq⟩ := GlobalTheory.UnitLemma.UnrExt.invol_eq_pow p hM s (fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [hs, hs, hττ]) (by
    obtain ⟨x, hx⟩ := hne
    exact ⟨residue S x, by rw [hs]; exact hx⟩)
  have h1 : ∀ x, residue S (τ x) = residue S x ^ M := fun x => by rw [← hs, hsq]
  refine ⟨h1, fun w hw => ?_⟩
  have hcard2 : 2 ≤ M ^ 2 := by
    have : 1 < Nat.card (ResidueField S) := Finite.one_lt_card
    omega
  set N := M ^ 2 - 1 with hN
  have hNk : (N : ResidueField S) ≠ 0 := by
    haveI := Fintype.ofFinite (ResidueField S)
    have h0 : ((N + 1 : ℕ) : ResidueField S) = 0 := by
      rw [show N + 1 = M ^ 2 by omega, ← hM, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    intro h
    simp [h] at h0
  refine GlobalTheory.UnitLemma.UnrExt.root_unique (residue S) (ker_residue) (X ^ N - 1 : S[X])
    (by simpa using X_pow_sub_one_separable_iff.2 hNk) (a := τ w) (b := w ^ M) ?_ ?_ ?_
  · simp [← map_pow, hw]
  · simp only [eval_sub, eval_pow, eval_X, eval_one]
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow, sub_self]
  · rw [h1, map_pow]

end GlobalTheory.UnitLemma.InvolRes
