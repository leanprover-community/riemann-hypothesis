module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupScalarAtFinitePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFramesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TOfFixFirstStatement
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop.UnitAtLevel
end GlobalTheory.MiTop.UnitAtLevel
namespace GlobalTheory.MiTop


theorem centralRatio_stabLoc_atLevel_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hrS u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hz hzc k hk he v hv
  have hm : 0 < D.R.m := by unfold Ranks.rS at hrS; omega
  have hfr := (_root_.GlobalTheory.T.selfDual_and_frame_of_pkHyp W hW 0 hm).2
  have hkSt := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) (W.Q.Rl.βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hfr k).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG hk) v
  obtain ⟨e, α, hl⟩ := _root_.GlobalTheory.T.level_place_frame_exists_alt W hW hrS v hv
  obtain ⟨ζ, hζ⟩ := GlobalTheory.T.center_adelicUnitaryGroup_scalar_at_finitePlace D (D.sp.Y 0) z hzc v
  have hpos : 0 < (D.sp.Y 0).rank := by
    have := B.d.rank_add
    omega
  obtain ⟨ι, hιζ, hζinv⟩ := GlobalTheory.MiTop.UnitAtLevel.inv_of_scalar hpos _ ζ hζ
  have htinv : (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)))⁻¹ =
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k))⁻¹ *
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')))⁻¹ *
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z))⁻¹) := by
    rw [he, map_mul, map_mul, map_mul, map_mul, mul_inv_rev, mul_inv_rev]
  have hkinv : ∀ y, y ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v ↔
      Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k))⁻¹).val y ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
    have h := GlobalTheory.AdelicU.mem_stabLoc.1 (inv_mem hkSt)
    intro y
    have h2 := h y
    rw [map_inv] at h2
    exact h2
  have key : ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v ↔
      ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * (ι * c) ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
    intro c
    rw [← hl u f B (_root_.GlobalTheory.MiTop.PlacedConditions.placed f B hP) a₀ a hA c, ← hl u' f' B' (_root_.GlobalTheory.MiTop.PlacedConditions.placed f' B' hP') a₀' a' hA' (ι * c), htinv, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hζinv, GlobalTheory.MiTop.UnitAtLevel.smulOne_mulVec, smul_smul]
    exact (hkinv _).symm
  obtain ⟨hζO, hιO⟩ := GlobalTheory.MiTop.UnitAtLevel.mem_of_shift (GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) _ ζ ι
    ⟨α, Units.mul_inv α⟩ hιζ key
  refine GlobalTheory.AdelicU.mem_stabLoc.2 ?_
  intro y
  rw [hζ, GlobalTheory.MiTop.UnitAtLevel.smulOne_mulVec]
  constructor
  · intro hy
    have := Submodule.smul_mem _ (⟨ζ, hζO⟩ : GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) hy
    rwa [Subring.smul_def] at this
  · intro hy
    have := Submodule.smul_mem _ (⟨ι, hιO⟩ : GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) hy
    rwa [Subring.smul_def, smul_smul, hιζ, one_smul] at this
end GlobalTheory.MiTop
end
end
