module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoLocAppendSingleton
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentificationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLiftOfPairLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceImage

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem parUpRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.ParUpRec D.nd D.naut i := by
  intro D T hθ hpair hbc hsplit hrep i x hx Sig hSig
  have h := GlobalTheory.ParUpRoad.main _ _ _ D.nd D.naut hθ (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut T).1
    (fun i => splitLift_of_pairLift _ _ _ D.nd D.naut i (hpair i))
    (fun i => GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsplit i) (hrep i))
  exact (GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage.thetaTMapsIntoEig_iff_map_le D.nd D.naut).1 h i x Sig hx hSig

end GlobalTheory.RowTie
