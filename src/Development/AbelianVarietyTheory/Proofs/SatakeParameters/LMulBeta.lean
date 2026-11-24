module

public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

def Clos {R : Type} [CommRing R] (S : Subring R) (π : R) : Subring R where
  carrier := {x | ∀ n : ℕ, ∃ s ∈ S, π ^ n ∣ x - s}
  mul_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s * s', mul_mem hs hs', a * c' + s' * c, ?_⟩
    linear_combination a * hc' + s' * hc
  one_mem' := fun n => ⟨1, one_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s + s', add_mem hs hs', c + c', ?_⟩
    linear_combination hc + hc'
  zero_mem' := fun n => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha n
    obtain ⟨s, hs, c, hc⟩ := ha n
    refine ⟨-s, neg_mem hs, -c, ?_⟩
    linear_combination -hc

variable {l : ℕ} [Fact l.Prime]

def linv (l : ℕ) [Fact l.Prime] : Per.AinfP l := ((GlobalTheory.RingBasics.isUnit_l l).unit⁻¹ : (Per.AinfP l)ˣ)

theorem mul_linv : ((l : ℕ) : Per.AinfP l) * linv l = 1 := (GlobalTheory.RingBasics.isUnit_l l).mul_val_inv

def beta (ϖ : Per.Fl l) : Per.AinfP l :=
  linv l * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - 1

theorem l_mul_beta (ϖ : Per.Fl l) : ((l : ℕ) : Per.AinfP l) * beta ϖ =
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - ((l : ℕ) : Per.AinfP l) := by
  have h := mul_linv (l := l)
  rw [beta]
  linear_combination algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) * h

def Sa (ϖ : Per.Fl l) : Subalgebra (Per.Ainf l) (Per.AinfP l) := Algebra.adjoin _ {beta ϖ}

def Sg (ϖ : Per.Fl l) : Subring (Per.BdRp l) :=
  (Sa ϖ).toSubring.map (algebraMap (Per.AinfP l) (Per.BdRp l))

def betaD (ϖ : Per.Fl l) : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ)

end GlobalTheory.Pst.StLat
