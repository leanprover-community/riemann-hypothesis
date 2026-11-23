module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidalStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeTwistedCuspParts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DictStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobEigTwEqInvValVStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQStatement
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.EigStrSplit.str_split_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw hsp
  obtain ⟨Q, hQx, hu, hBQ⟩ := _root_.GlobalTheory.T.theta_eigen_compatibility_eighth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw hsp
  obtain ⟨-, Sig, ⟨P0, hP0, hbc⟩, hgood⟩ := hx
  have hcusp := GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal D htl i x Sig ⟨P0, hP0, hbc⟩ hgood
  obtain ⟨hS, hQ⟩ := _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_tieLab hL D P X hA h41 htl i w hw
  have hz := _root_.GlobalTheory.T.isSplit_at_good_heightOne_place_of_used0 hAF hL D P X hA htl i hμ j hj w hw hsp
  obtain ⟨B', e, hB'⟩ := _root_.GlobalTheory.T.isSplit_of_isBCV_twistIso_of_isCuspIso hAF hL D P h41 h7 htl i x Q P0 Sig hQx hP0 hcusp hbc w hsp hS hQ hu _ hz
  exact ⟨B', hBQ.trans e, hB'⟩
end
