module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

theorem _root_.GlobalTheory.T.adelicGLLastRow_and_detModule_under_left_multiplication : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ),
    (∀ (γ : GL (Fin (m + 1)) E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) =
      Matrix.vecMul (algebraMap E (Ad E) ∘ Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val) g.val) ∧
    (∀ g : GA E (m + 1), GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val) ∧
    (∀ γ : GL (Fin (m + 1)) E, IsMir m γ → Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1) ∧
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (blkU y * g) = GlobalTheory.ZEul.lastRow g ∧
      GlobalTheory.RSnm.detAbs (blkU y * g) = GlobalTheory.RSnm.detAbs g) ∧
    (∀ (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)),
      GlobalTheory.RSnm.detAbs (uGL X * g) = GlobalTheory.RSnm.detAbs g) := by
  first | (exact @GlobalTheory.UnfoldRows.rows_main) | (exact GlobalTheory.UnfoldRows.rows_main) | (intros; apply GlobalTheory.UnfoldRows.rows_main  <;> assumption)
