module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import GroundTheory.GlobalFields.LocalAtPlace
public import GroundTheory.LocalFields.PadicLogSeries
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModAbs

theorem ordL_eq_ord {E : Type} [Field E] [NumberField E] (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    ordL x = GroundTheory.LocalField.ord x := by
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord hx
  have hv : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  unfold ordL
  rw [dite_eq_right hv]
  have : WithZero.unzero hv = Multiplicative.ofAdd (-GroundTheory.LocalField.ord x) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h2]
    rfl
  rw [this, toAdd_ofAdd, neg_neg]

theorem haar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  intro E _ _ w x hx
  have h1 := GroundTheory.LocalField.distribHaarChar_eq_modulus (K := w.adicCompletion E) (Units.mk0 x hx)
  have h3 : (GroundTheory.LocalField.residueCard (w.adicCompletion E)) = Ideal.absNorm w.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  rw [h1, Units.val_mk0, GroundTheory.LocalField.modulus_of_ne_zero hx, h3]
  unfold absHalf
  rw [ordL_eq_ord w hx]
  have hq : (0 : ℝ) ≤ ((qV E w : ℕ) : ℝ) ^ (-GroundTheory.LocalField.ord x) := zpow_nonneg (Nat.cast_nonneg _) _
  rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  simp [qV]

end GlobalTheory.ModAbs
