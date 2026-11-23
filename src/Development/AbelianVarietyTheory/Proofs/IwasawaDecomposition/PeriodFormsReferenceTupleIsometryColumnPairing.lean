module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetricStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelationPreservesLevelFormLatticeNormStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetricStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

attribute [local instance] GlobalTheory.Mem.Col2.starE



theorem eMt0_isometry : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  intro K B f T w hO hF hP P x hη u F G
  show inner ℂ (P.q.e.e0 u F) (P.q.e.e0 u G) = _
  have hN : ∀ m : (Df.MtHL w.I P.hX w.I.mu0).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL w.I P.hX w.I.mu0).b (Df.MtHL w.I P.hX w.I.mu0).X
      (InfinitePlace.mk B.embLL) m = ‖P.q.per.e w.I.mu0 (Df.toCx w.I P.hX w.I.mu0 m)‖ :=
    GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr w.I.mu0 (P.q.t.tA true w.I.mu0) (P.q.per.e w.I.mu0) (P.q.per.crd w.I.mu0)
  have hin : ∀ y y' : Df.MtCx w.I w.I.mu0, inner ℂ (P.q.per.e w.I.mu0 y) (P.q.per.e w.I.mu0 y') = Df.cSum w.I P.hX w.I.mu0 y y' := by
    intro y y'
    obtain ⟨-, ⟨j, hj⟩, -, hsp⟩ := GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis w.I P.hX w.I.mu0
    obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
    have hspan : Submodule.span ℂ (Set.range j) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, hj _⟩)
    exact Df.inner_eq_of_norm_sq B.embLL j hspan k hk (P.q.per.e w.I.mu0).toLinearMap (Df.cSum w.I P.hX w.I.mu0) (fun m => by
      rw [hj, LinearEquiv.coe_toLinearMap, ← hN m, GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric w.I P.hX w.I.mu0 m]) y y'
  have key : ∀ F : ((w.D x.o.Z).mem u).P.Mt,
      Df.SameForm w.I w.l u w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) F := fun F => by
    have h := P.q.per.ref u ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F))
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  have h1 : ∀ F : ((w.D x.o.Z).mem u).P.Mt, P.q.e.e0 u F = P.q.per.e w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) :=
    fun F => ((P.q.per.e w.I.mu0).apply_symm_apply _).symm
  rw [h1 F, h1 G]
  exact (hin _ _).trans (GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u w.I.mu0 F G _ _ (key F) (key G)).symm

end GlobalTheory.Mem.R3.Rw.St

end
