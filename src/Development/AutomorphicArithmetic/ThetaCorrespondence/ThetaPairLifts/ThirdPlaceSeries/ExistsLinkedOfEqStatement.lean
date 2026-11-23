module

public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLinkedOfEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.eta_size_recursion_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt | exact _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt <;> assumption)
end
