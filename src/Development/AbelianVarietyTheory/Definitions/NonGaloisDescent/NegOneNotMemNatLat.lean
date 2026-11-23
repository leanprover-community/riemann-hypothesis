module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def eLast (R : Type*) [CommRing R] (a : ℕ) : Fin a → R := fun i => if (i : ℕ) + 1 = a then 1 else 0

theorem secRow_eLast {R : Type*} [CommRing R] : secRow (eLast R a) = 1 := by
  ext i j
  simp only [secRow, eLast, Matrix.of_apply, Matrix.one_apply]
  by_cases h : (i : ℕ) + 1 = a
  · rw [if_pos h]
    by_cases h2 : (j : ℕ) + 1 = a
    · rw [if_pos h2, if_pos (Fin.ext (by omega))]
    · rw [if_neg h2, if_neg (fun e : i = j => h2 (e ▸ h))]
  · rw [if_neg h]



omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem secInv_eLast : secInv (eLast (Cinf E) a) = 1 := by
  unfold secInv
  split_ifs with h
  · rw [inv_eq_one]; exact Units.ext secRow_eLast
  · rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_mul (x : ℝ) (g h : GA E a) : detPow E a x (g * h) = detPow E a x g * detPow E a x h := by
  simp [detPow]



omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_ratGL (x : ℝ) (γ : GL (Fin a) E) : detPow E a x (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = diagUnits E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map (algebraMap E (Ad E)) γ)
  have h2 := (GlobalTheory.HeckeGal.Model.absPow E x).2.2 (Matrix.GeneralLinearGroup.det γ)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, h, h2]; simp








end GlobalTheory.RSJ.Model
