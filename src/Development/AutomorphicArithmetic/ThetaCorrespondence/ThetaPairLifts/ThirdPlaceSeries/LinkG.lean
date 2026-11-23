module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
public import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
public import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.closed_linkG_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkG Fm := by
  intro 𝒜 sel hduty
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hG2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.G.Adm2F Fm :=
    Closed.of_class fun Fm _ hc => admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)
  have hGt : Closed (D3 3 𝒜) fun Fm _ => Formalism.L2.G.GroupCompatibilityFamily Fm :=
    Closed.of_class fun Fm _ hc => _root_.Formalism.L2.group_compatibility_of_second_layer_family Fm (hRec Fm (d3_a hc))
  have lG := Formalism.L2.G.linkG_concrete5 (D3 3 𝒜) hGt hG2
  exact lG
end
end
