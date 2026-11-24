module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuples
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.Pdv.oneTie_jointsAt_all | exact GlobalTheory.Pdv.oneTie_jointsAt_all | (intros; apply GlobalTheory.Pdv.oneTie_jointsAt_all <;> assumption)
