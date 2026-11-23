module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientLatticeSpan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiValStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPartStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
theorem adForm_eq_levelTrace_singleSeries' : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ h ∈ GfC (Vc (Fm.D x i) j), ∀ w' : ((R2 p).cV j).W, InCoefLat (R2 p) j h w' →
  ∃ y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)), ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j y (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) h w' v) := by
  intro _ _ _ _
  have hR := _root_.GlobalTheory.T.rational_estimate_statement'
  have hC := _root_.GlobalTheory.T.twisted_character_rational_values'
  have hN := _root_.GlobalTheory.T.exists_isLevelLift_at_twisted_points
  unfold _root_.GlobalTheory.BigOn.RationalityStatement' _root_.GlobalTheory.BigOn.AtPtsAlt at hR
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hC hN ⊢
  refine ((hR.and hC).and hN).imp fun Fm CH _ H => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := H
  obtain ⟨x0, hE⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx hle i p hp hM w hw j h hh w' hw' => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hE x hx hle i p hp
  obtain ⟨θ, hθ⟩ := a1 hM _ hw j
  obtain ⟨hCh, hOk, hU, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hS : GlobalTheory.TraceIncl.HidaSetting (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w)) :=
    ⟨hCh.lev, hCh.grp.red_L, hCh.fam.tie, hCh.models, hCh.thP, hU, ⟨_, ((fw2 p).hv₀ j _).1⟩, (hOk.lifts _ _).act,
      fun g0 κ κ' k1 k2 => GlobalTheory.VecInv.omega_lifts_vP (R2 p) hCh.lev hCh.models.inf hCh.thP.ωP hCh.thP.vP j _ g0 κ κ' k1 k2⟩
  obtain ⟨y, -, hy⟩ := exists_adForm_levelTrace hS (a3 hM w hw j) (a2 hM w hw j) hθ hh hw'
  refine ⟨y, ?_, hy⟩
  obtain ⟨n, b, hbK, -, -, -, hsp⟩ := (fw2 p).ks j
  have hy0 := hsp.symm ▸ (Submodule.mem_top (x := y))
  refine Submodule.span_le.2 ?_ hy0
  rintro _ ⟨k, rfl⟩
  have hk : (p.nexp.fi j).e ((p.nexp.fi j).e.symm (b k)) = b k := (p.nexp.fi j).e.apply_symm_apply (b k)
  refine Submodule.subset_span ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 ?_, hk⟩
  first
    | exact hk.symm ▸ hbK k
    | exact (congrArg (fun z => z ∈ (p.R.FW j).WK) hk).mpr (hbK k)
    | (rw [hk]; exact hbK k)
end GlobalTheory.BigOn.Exp
end
end
