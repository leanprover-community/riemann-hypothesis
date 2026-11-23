module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem adele_eq_sInf_add_sFin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Ad E) :
    x = sInf E (pInf E x) + sFin E (pFin E x) := by
  refine Prod.ext ?_ ?_
  · change x.1 = infEq E ((infEq E).symm x.1) + 0
    simp
  · change x.2 = 0 + x.2
    simp

theorem psiN_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  intro E _ _ _ n u
  have h : GlobalTheory.Whittaker.superDiag u = sInf E (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) + sFin E (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by

    simp only [GlobalTheory.Whittaker.superDiag, sdM, map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact adele_eq_sInf_add_sFin _
  unfold GlobalTheory.JSW.psiN psiInf psiFin
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.WhitBump
