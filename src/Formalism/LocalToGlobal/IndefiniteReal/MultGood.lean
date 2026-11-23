module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩ := h
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a),
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩,
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩
  · unfold dualPar
    rw [Finset.image_image]
    ext ⟨x, s⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.rev a, by simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, ha⟩
  · obtain ⟨z, hz⟩ := hint (Fin.rev a)
    refine ⟨-z - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)

theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) : StrictAnti fun a : Fin R.r => lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at this
  have h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

def sgA (R : Ranks) (a : ℕ) : Bool := decide (a < R.k - 1 ∨ Even (a - (R.k - 1)))

theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin R.r => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := hpq ▸ odd_r R
  ext ⟨x, s⟩
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    cases a with
    | inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩
    | inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    by_cases hc : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩
      simp only [Sum.elim_inr]
      rw [show p + ((a : ℕ) - p) = a by omega]

end Formalism.IndefR.Mult
