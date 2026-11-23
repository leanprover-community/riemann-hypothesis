module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenAtInertStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrSplitStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandEigenStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamAtInertStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamSplitStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEigenCompatibilitySixth
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.EigStr.eigString_all_of_aux41_adm7_tieLab : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ i, GlobalTheory.NJoin.EigString X i := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy
  show y ≠ 0 → _
  intro hy0 hh hops
  classical
  let s : GlobalTheory.DownLift.Sys D := fun Pp d =>
    if hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y then hc.choose else 0
  have hs : GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) hh s y := by
    intro Pp d hG hLab
    have hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y :=
      (GlobalTheory.LPositivity.split_or_inert D Pp).elim
        (fun h1 => _root_.GlobalTheory.T.theta_eigen_compatibility_first_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops Pp hG h1 d hLab)
        (fun h1 => _root_.GlobalTheory.T.theta_eigen_compatibility_second_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops Pp hG h1 d hLab)
    simp only [s, dif_pos hc]
    exact hc.choose_spec
  let B : GlobalTheory.LFun.Fam D.host.E := fun w =>
    if hB : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank
        (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw then hB.choose else 0
  have hB : GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)))
      (Formalism.IndefR.Links.Vc D j).rank s B := by
    intro v hv w hw
    subst hw
    have hex : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank
        (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
      rcases GlobalTheory.LPositivity.split_or_inert D w with h1 | h1
      · exact _root_.GlobalTheory.T.theta_eigen_compatibility_third_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1
      · exact _root_.GlobalTheory.T.theta_eigen_compatibility_fourth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1
    show GlobalTheory.LFun.IsSysParam D.sp.cm.sig _ _ (s w) (B w)
    simp only [B, dif_pos hex]
    exact hex.choose_spec
  refine ⟨s, ⟨B, hB, fun w hw => ?_⟩, hs⟩
  rcases GlobalTheory.LPositivity.split_or_inert D w with h1 | h1
  · exact _root_.GlobalTheory.T.theta_eigen_compatibility_fifth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1
  · exact _root_.GlobalTheory.T.theta_eigen_compatibility_sixth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1
end
