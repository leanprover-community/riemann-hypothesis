module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegrality
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

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wordFrame_dualTuple_gram_integrality : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧ GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧ GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  first | exact @GlobalTheory.CovDom.frame_dual_lat | exact GlobalTheory.CovDom.frame_dual_lat | (intros; apply GlobalTheory.CovDom.frame_dual_lat <;> assumption)
