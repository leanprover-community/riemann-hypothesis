module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeCentralCharacterEqCompNorm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeInfinitesimalCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeLocalLanglandsAtTrivialTwist
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalBaseChangeInertCompatible
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.LiftRef
theorem baseChange_local_compatible_all_places_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → LiftAll (w.st Z).toD7 Rw := by
  intro hP hL
  have h := overRows_and_mono (_root_.GlobalTheory.T.infG_embTau_eq_neg_half_and_embTauBar_eq_half hP hL) (_root_.GlobalTheory.T.baseChange_localLanglands_at_trivial_twist_alt hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  have h' := overRows_and_mono h (_root_.GlobalTheory.T.sph_inert_cls_of_iso_typ_comap_ne_bot hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  refine overRows_and_mono h' (_root_.GlobalTheory.T.baseChange_infinitesimalCharacter_alt hP hL) ?_
  rintro K B f T w Z Wt hX z p0 Y ⟨⟨hc, hl⟩, hs⟩ hi Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨S, hS, hm, hloc⟩ := hl Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨μ, hμ, hcsd, hunr, heta⟩ := hc Rw a M tup Q hA hI ⟨j - 1, by omega⟩
  exact ⟨_, μ, ⟨hcsd, hunr, hs Rw a M tup Q hA hI j h1 h2 S hS hm, hloc μ hμ, heta, hi Rw a M tup Q hA hI j h1 h2 S hS μ hμ⟩⟩
end GlobalTheory.LiftRef
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.liftAll_of_parIn_of_mtInput : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → LiftAll (w.st Z).toD7 Rw := by
  exact @_root_.GlobalTheory.LiftRef.baseChange_local_compatible_all_places_alt
end
end
