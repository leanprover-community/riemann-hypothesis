module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
public import Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgreeStatement
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.DzGoodVec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsClassMapCorrespondence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCompIrrSmParamStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSupportCompatible
import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
theorem goodFTAll_of_local_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → LabTie D L → (∀ k, TameGen.DepthZeroCuspidal (D.host.g k)) → (∀ (I : Ident D) rc, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, DiscreteGroups.sglob.DzType.Rt.TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2)) → (∀ (I : Ident D) cp, IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hL D T Rw rep L hRow hDep hLT hDZ hTP hVec σ
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := _root_.GlobalTheory.T.exists_isRc_classMap_correspondence hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc hL D T I rc hrc Rw rep hRow hDep
  have hP : DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc :=
    DiscreteGroups.sglob.DzType.Rt.labParamLe_of D L rc hG (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D T I rc hrc) hDZ (hTP I rc hrc)
  have hSC := GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree hG D L hLT
  obtain ⟨V, _, _, ρ, W, x, hconj, hx0, hxW, hxe⟩ := hVec I cp hcomp σ
  exact _root_.DiscreteGroups.sglob.DzType.Rt.good_of_vector_row_m D Rw L rc cp hLT hP hcls hSC hcp V ρ W σ hconj x hx0 hxW hxe
end DiscreteGroups.sglob.DzType.Rt
end
