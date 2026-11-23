module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsoLocAppendSingleton
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharEtaBack
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section



section
noncomputable section
namespace GlobalTheory.GoodDepthZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
theorem main_alt_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → Formalism.MainNotions.N.GlobalDatumDepthZeroCondition D := by
  intro D hT hA h41 _ a x hx Sig hSig k v
  obtain ⟨-, Sig', hSig', hgood⟩ := hx
  have hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := hA.2.2
  have hL := charSum_of_tie D hT.1 hc
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨P', hP', hB'⟩ := id hSig'
  have hperm := ((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'
  have e1 := GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)
  rw [GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL] at e1
  have e2 := congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1
  simp only [lpChar_eta_back D hT.1] at e2
  rw [GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton] at e2
  rw [hc _ _ _ _ e2]
  exact GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v
end GlobalTheory.GoodDepthZero
end
end
