module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.IsQgOfOver
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurtherStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzLoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisConjPlaceDual
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
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH

@[expose] public section



section
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
theorem depthZero_tame_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf →
    DepthZ D := by
  intro hP hS hL D P hrow hlab hchi
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hrow
  have hfix : ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
      TameLP D (D.naut.locV i PI (D.naut.plGw k v)) := by
    intro i PI k v
    have hw := GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
    have htame := _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw hL D P S hT i k v hw
    have hTB := _root_.GlobalTheory.T.type_block_of_tame_at_split_place hL D P S hT i _ hw ⟨k, D.naut.plGw_over k v⟩ htame
    obtain ⟨x, hx0, hx⟩ := hTB.2 PI
    have hfixd : x ∈ GlobalTheory.PRep.fixed ((S i _ hw).rep PI).π
        (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
      intro h
      have h' : ((S i _ hw).rep PI).π h x = x := GlobalTheory.JacBlock.KOne_le_stab htame hx h.2
      simpa using h'
    have hwild := _root_.GlobalTheory.DepthZeroLoc.main_m_alt hP.bz hS hL D _ _ ((S i _ hw).rep PI) ⟨x, hfixd, hx0⟩
      (UpperTheory.One.M.isQg_of_over D k _ (D.naut.plGw_over k v))
    intro σ hσI hσW
    have hd : D.naut.lpDim (D.naut.locV i PI (D.naut.plGw k v)) = D.R.r + D.R.t := by
      rw [← P.T.dim, (S i _ hw).locV PI, (hLaws i _ hw).dim]
    rw [P.T.inePol _ _ σ hσI, (S i _ hw).locV PI, hT.rc i _ hw, hwild σ hσW, hd]
  intro i PI k w hw
  obtain ⟨v, rfl | hc⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact hfix i PI k v
  · exact ((_root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hlab) i PI k v w hc).2.1 (hfix i PI k v)
end GlobalTheory.DepthZeroTame
end
end
end
