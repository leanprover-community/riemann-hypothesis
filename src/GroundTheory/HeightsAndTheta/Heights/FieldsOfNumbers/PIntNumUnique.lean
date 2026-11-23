module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem IntNumUnique.proof (h1 : CutRational.Statement.{u}) (h2 : IntNumBase.Statement.{u})
    (h3 : ExistsForm.Statement.{u}) (h4 : DivCycleSupport.Statement.{u}) :
    IntNumUnique.Statement.{u} := by
  intro F _ K _ _ ι _ N hN P hP n
  induction n generalizing P with
  | zero =>
    intro hdim bs
    have hbs : bs = ![] := Subsingleton.elim _ _
    subst hbs
    rw [hN.base P hP hdim]
    obtain ⟨-, h⟩ := h2 F K ι P hP hdim
    rw [h]
    have := hP.isPrime
    simp [resDeg, hP.isPrime]
  | succ n ih =>
    intro hdim bs
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ := h3 F K ι P hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    rw [hbs, hN.cut P n hP hdim bf bg f g hf hg hfP hgP,
      h1 F K ι P hP n hdim bf bg f g hf hg hfP hgP]
    unfold cycEval
    congr 1
    funext W
    by_cases hW : ratDiv P f g W = 0
    · rw [hW, zero_mul, zero_mul]
    · have hsupp : IsMultiProjPrime W ∧ relDim W = (n : ℕ) := by
        unfold ratDiv at hW
        by_cases hfW : divCycle P f W = 0
        · have hgW : divCycle P g W ≠ 0 := by
            intro h
            apply hW
            rw [hfW, h, sub_zero]
          exact h4 F K ι P hP n hdim bg g hg hgP W hgW
        · exact h4 F K ι P hP n hdim bf f hf hfP W hfW
      simp only [ih W hsupp.1 hsupp.2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
