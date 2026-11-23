module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfConditions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeStdTwCoverStatement
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowPointLoc
theorem main_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) :
    GlobalTheory.SplitRead.RowPoint D.nd D.naut := by
  intro i σ hne
  obtain ⟨Q, hQ⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ :=
    GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D P.M P.H.hecke P.H.av P.H.cover (_root_.GlobalTheory.T.heckeStdTw_cover' hL D P) i σ Q hQ
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hl : D.nd.l i' = D.nd.l i := by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]
  obtain ⟨φ, hφ⟩ := P.H.hecke.sameO i' i hj hw
  refine ⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩
  exact continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ
end GlobalTheory.RowPointLoc
end
