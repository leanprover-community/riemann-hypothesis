module

import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FinsetCAR
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Finset

noncomputable section

namespace CompanionTheory.D.LK.Car

variable {n : ℕ}

theorem key_inj {i j : Pos n} (h : key i = key j) : i = j := by
  apply Subtype.ext (finProdFinEquiv.injective (Fin.ext ?_))
  change (i.1.2 : ℕ) + n * (i.1.1 : ℕ) = (j.1.2 : ℕ) + n * (j.1.1 : ℕ)
  unfold key at h
  simpa [Nat.mul_comm, Nat.add_comm] using h

def tw (i j : Pos n) : ℂ := if key j < key i then -1 else 1

theorem tw_self (i : Pos n) : tw i i = 1 := by
  simp [tw]

theorem tw_mul_self (i j : Pos n) : tw i j * tw i j = 1 :=
  _root_.CompanionTheory.FinsetCAR.tw_mul_self key i j

theorem tw_swap {i j : Pos n} (h : i ≠ j) : tw j i = -tw i j :=
  _root_.CompanionTheory.FinsetCAR.tw_swap key (fun _ _ h => key_inj h) h

theorem sg_mul_self (i : Pos n) (A : Finset (Pos n)) : sg i A * sg i A = 1 :=
  _root_.CompanionTheory.FinsetCAR.sg_mul_self key i A

theorem sg_insert (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_insert key i h

theorem sg_erase (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_erase key i h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl

theorem cre_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : Pos n) : (ann i * ann j + ann j * ann i : Module.End ℂ (Cn n V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_ann key (fun _ _ h => key_inj h) i j

theorem cre_cre (i j : Pos n) : (cre i * cre j + cre j * cre i : Module.End ℂ (Cn n V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.cre_cre key (fun _ _ h => key_inj h) i j

theorem ann_cre (i j : Pos n) :
    (ann i * cre j + cre j * ann i : Module.End ℂ (Cn n V)) = if i = j then 1 else 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_cre key (fun _ _ h => key_inj h) i j


end CompanionTheory.D.LK.Car
