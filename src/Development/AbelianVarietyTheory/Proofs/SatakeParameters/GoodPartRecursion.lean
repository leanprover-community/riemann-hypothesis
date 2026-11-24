module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentificationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
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

@[expose] public section

namespace GlobalTheory.Proof.GoodComponentRecursion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem goodPartRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.GoodPartRec D.nd D.naut i := by
  intro D hW h1 hlift hpt hbc hsp i
  exact GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts D.nd D.naut i h1
    (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut hW).1 (hlift i) (hpt i)
    (GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsp i))

end GlobalTheory.Proof.GoodComponentRecursion
