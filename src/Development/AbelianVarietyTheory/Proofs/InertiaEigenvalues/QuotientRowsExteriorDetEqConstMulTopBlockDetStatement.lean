module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries

theorem _root_.GlobalTheory.T.quotientRowsExteriorDet_eq_const_mul_topBlockDet : ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  first | exact @GlobalTheory.dU_eq_const_mul_det_topL_translate | exact GlobalTheory.dU_eq_const_mul_det_topL_translate | (intros; apply GlobalTheory.dU_eq_const_mul_det_topL_translate <;> assumption)
