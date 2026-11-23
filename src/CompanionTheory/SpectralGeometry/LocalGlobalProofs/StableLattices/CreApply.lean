module

import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FinsetCAR
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Finset CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.ChainCAR

variable {n : ℕ} {ε : Fin n → Bool}

theorem key_inj {i j : NC ε} (h : key i = key j) : i = j := by
  apply Subtype.ext (finProdFinEquiv.injective (Fin.ext ?_))
  change (i.1.2 : ℕ) + n * (i.1.1 : ℕ) = (j.1.2 : ℕ) + n * (j.1.1 : ℕ)
  unfold key at h
  simpa [Nat.mul_comm, Nat.add_comm] using h

def tw (i j : NC ε) : ℂ := if key j < key i then -1 else 1

theorem tw_self (i : NC ε) : tw i i = 1 := by
  simp [tw]

theorem tw_mul_self (i j : NC ε) : tw i j * tw i j = 1 :=
  _root_.CompanionTheory.FinsetCAR.tw_mul_self key i j

theorem tw_swap {i j : NC ε} (h : i ≠ j) : tw j i = -tw i j :=
  _root_.CompanionTheory.FinsetCAR.tw_swap key (fun _ _ h => key_inj h) h

theorem sg_mul_self (i : NC ε) (A : Finset (NC ε)) : sg i A * sg i A = 1 :=
  _root_.CompanionTheory.FinsetCAR.sg_mul_self key i A

theorem sg_insert (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_insert key i h

theorem sg_erase (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_erase key i h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl

theorem cre_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : NC ε) : (ann i * ann j + ann j * ann i : Module.End ℂ (Ch ε V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_ann key (fun _ _ h => key_inj h) i j

theorem cre_cre (i j : NC ε) : (cre i * cre j + cre j * cre i : Module.End ℂ (Ch ε V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.cre_cre key (fun _ _ h => key_inj h) i j

theorem ann_cre (i j : NC ε) :
    (ann i * cre j + cre j * ann i : Module.End ℂ (Ch ε V)) = if i = j then 1 else 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_cre key (fun _ _ h => key_inj h) i j

theorem car : CompanionTheory.D.DSIC.CAR := fun _ _ _ _ _ i j => ⟨ann_ann i j, cre_cre i j, ann_cre i j⟩

end GlobalTheory.CompanionTheory.ChainCAR
