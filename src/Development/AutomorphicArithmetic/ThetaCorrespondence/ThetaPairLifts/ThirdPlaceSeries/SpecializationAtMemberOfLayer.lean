module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PinAtOfSide
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
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.PinLayer

theorem specialization_at_member_of_layer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a P := by
  intro hP hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  have e' : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  have hT : TypesTrue (w.D Z).ntypes (TC.cf w.I w.l Z).P (TC.cf w.I w.l Z).W := by
    show TypesTrue _ w.I.C.P w.I.C.W
    rw [w.C_eq]
    exact t.grp
  have hEl : Elem (w.D Z) := by
    refine ⟨fun y => ?_, fun j g => ((w.D Z).hc ((w.D Z).eTau.symm g)).e_int j, fun v hv => ?_⟩
    · exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
        (starRingEnd (w.D Z).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
    · have hc : ∀ p ∈ (w.D Z).host.levelPrimes, p.Prime ∧ p % ((w.D Z).host.QS * (w.D Z).host.q * (w.D Z).host.d) = 1 :=
        (w.st Z).B.level_cond
      rcases hv with hv | hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.1 v hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.2 v hv
  exact _root_.GlobalTheory.PinLayer.pinAt_of_side_alt c.a hP.greenC hT (GlobalTheory.HeightCounting.Up.valLL0_colW w Z)
    (fun σ => Formalism.IndefR.principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT σ)) c.row.rep_eq
    (fun σ σ' h => t.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) hEl
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) e'.labc e'.zeta
end GlobalTheory.PinLayer
end
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a P := by
  first | exact @_root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt | exact _root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt | (intros; apply _root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt <;> assumption)
end
end
