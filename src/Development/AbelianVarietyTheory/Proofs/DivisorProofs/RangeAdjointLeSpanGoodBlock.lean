module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsEquivariantTwistedAndPlainModelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointCompositeLiftLeSpanBlockEigenspacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThetaLiftLeBlockEigenspaceSpanStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInfOfLinearIndependent
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.AdjBlockSpan

open GlobalTheory.AdjBlock

theorem range_adjoint_le_span_good_block : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → R.PGEquiv F → (∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A3.A.fam.R t).ZHg A3.A.X : Set (A3.A.fam.R t).S.Forms))) ∧ ∀ i t, LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤ Submodule.span ℂ (R.jV i t '' ((A3.A.fam.L i t).ZHg A3.A.X : Set (A3.A.fam.L i t).S.Forms)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hE hS hPG
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hG := GlobalTheory.T.lifts_equivariant_twisted_and_plain_models R F hW.phase hPG
  have hOk2 := hOk.ok2
  refine ⟨fun t => ?_, fun i t => ?_⟩
  · have h1 := GlobalTheory.T.range_adjoint_compositeLift_le_span_blockEigenspaces R.toRealDat F.lv2 hLI hOk2 hC hS t
    have h2 := GlobalTheory.AdjGood.range_adjoint_Th_le_span_good R.toRealDat F.lv2 hOk2 hC hG.1 t
    have hli := (model_form (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t)).1
    have h3 := GlobalTheory.span_image_inf_of_linearIndependent _ (R.jX t) _ hli ((A3.A.fam.R t).ZH) ((A3.A.fam.R t).goodF A3.A.X)
    exact (le_inf h1 h2).trans h3.le
  · have h1 := GlobalTheory.T.range_adjoint_thetaLift_le_blockEigenspaceSpan R.toRealDat F.lv2 hLI hOk2 hC hS i t
    have h2 := GlobalTheory.AdjSpanLift.range_adjoint_lift_le R.toRealDat F.lv2 hOk2 hC hG.2 i t
    have hli := (model_form (R.B.L i t).pres (R.HV i t) (hC.models.HV i t) (hC.models.jV i t)).1
    have h3 := GlobalTheory.span_image_inf_of_linearIndependent _ (R.jV i t) _ hli ((A3.A.fam.L i t).ZH) ((A3.A.fam.L i t).goodF A3.A.X)
    exact (le_inf h1 h2).trans h3.le

end GlobalTheory.AdjBlockSpan

end
