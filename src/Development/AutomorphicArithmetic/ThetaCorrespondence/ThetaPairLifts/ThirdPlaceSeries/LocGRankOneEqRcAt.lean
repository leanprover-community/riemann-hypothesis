module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecUnit
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.ParLawsBare
open GlobalTheory.RowTie GlobalTheory.NPin Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil in
theorem e_locG_eq_rcAt_ofDet_of_isComp {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w 1 (GlobalTheory.SplitRead.Irr.ofDet 1 ξ h.1) := by
  have : IsCMField D.host.E := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc (v : PlE D.host) :
      T.e v (D.naut.locG π v) =
        ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := by
    rw [cg.loc, hχ', CGu.ofChar_equivChar]
    rfl
  have unr' (v : PlE D.host) : D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := by
    rw [T.unr, hloc v]
    exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' (D.nd.plOm.2 v)
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · change χ'.loc v x * (χ.loc v x)⁻¹ = 1
      rw [u2 x hx, u1 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ w, fun x => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep]
  rw [hchar]
  rfl
theorem rankOneUnitary_of_charSide {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (cs : CharSide D cf) : RankOneUnitary T := by
  intro π w σ _ α hα
  obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.HeckeComp.main D.host.E (cs.e1 π).1 w
  have he := _root_.GlobalTheory.ParLawsBare.e_locG_eq_rcAt_ofDet_of_isComp T cg cs π w ξ hξ
  rw [WDTie.eig, he] at hα
  unfold WD.inePol at hα
  split_ifs at hα with hσ
  · exact _root_.UpperTheory.Zero.LLC.IsRecT.recUnit (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) ξ
      (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1) (hξu (cs.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα
  · simp at hα
end GlobalTheory.ParLawsBare
end
end
