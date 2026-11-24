module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselLowestVectorLocalMassEqTransported
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

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.l2SG_phiOf_eq_l2SG_wT_of_goodLoc : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  first | exact @GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | exact GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | (intros; apply GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported <;> assumption)
