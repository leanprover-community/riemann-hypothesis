module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRowSameWeightSameLocalData
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

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.terms_same_row_same_weight_same_localData : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' ∧ (nmlOf Y u u' t = nmlOf Y u u' t' → ∀ (p : PlF D) (P : LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), P.RelG (LocNG.theta (Y.M p)) → ∀ d, Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) → Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.toTerm.lam (lf D (X.Fu u)) (Quot.out t'.toTerm.cls).1 (Tu D u) (Tu D u'))) := by
  first | exact @GlobalTheory.LocOver.TermSame.same | exact GlobalTheory.LocOver.TermSame.same | (intros; apply GlobalTheory.LocOver.TermSame.same <;> assumption)
