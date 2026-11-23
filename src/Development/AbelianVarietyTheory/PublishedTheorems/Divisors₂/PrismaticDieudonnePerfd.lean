module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import ReciprocityTheory.DualLattices.AinfFacts
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

structure CycPerfd (p : ℕ) [Fact p.Prime] : Type 1 where
  R : Type
  [ring : CommRing R]
  [nonunit : Fact ¬IsUnit (p : R)]
  [complete : IsAdicComplete (span {(p : R)}) R]
  reg : IsSMulRegular R (p : R)
  ε : PreTilt R p
  zeta_zero : zeta ε 0 = 1
  surj : Function.Surjective (fontaineTheta R p)
  ker_eq : RingHom.ker (fontaineTheta R p) = span {xi ε}

attribute [instance] CycPerfd.ring CycPerfd.nonunit CycPerfd.complete

def CycPerfd.Over {p : ℕ} [Fact p.Prime] (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R) : Prop :=
  (∀ a, fontaineTheta S'.R p (α a) = algebraMap S.R S'.R (fontaineTheta S.R p a)) ∧
    (∀ a, α (frobenius a) = frobenius (α a)) ∧ α (teichmuller p S.ε) = teichmuller p S'.ε

def CycPerfd.ofIntegers (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) : CycPerfd p where
  R := O
  reg := fun a b h => sub_eq_zero.1 (ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by
    have h' : (p : O) * a = (p : O) * b := h
    rw [pow_one, sub_mul, mul_comm a, mul_comm b, h', sub_self]))
  ε := ε
  zeta_zero := (zeta_succ_pow ε 0).symm.trans hε.pow_eq_one
  surj := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  ker_eq := ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε


end GlobalTheory.Published
