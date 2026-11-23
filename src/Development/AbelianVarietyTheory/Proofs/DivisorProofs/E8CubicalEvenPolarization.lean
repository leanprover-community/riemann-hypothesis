module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8PowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8



theorem exists_cp_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  intro hL _ _ V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  let P₁ : GlobalTheory.UU.CP G₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₁ W
  refine ⟨Pc, hPc, ?_⟩
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D', ⟨pD⟩⟩ := GlobalTheory.PowDegData.main hL.globalFns V₁ _ D₀ 8
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ A₀ 8
  obtain ⟨U', -⟩ := GlobalTheory.PowUnif.main hL.globalFns V₁ _ 8 D₀ D' A₀ A' G₀ (powObj G₀ 8) pD pA (powIsPowGrp G₀ 8)
    U₀.toUnifPre
  have hp : IsProper (pullback.snd (powObj G₀ 8).hom (jK V₁)) := by
    have := A'.isAb.proper
    have e : pullback.snd (powObj G₀ 8).hom (jK V₁) = U'.gen.hom.left ≫ A'.A.hom := (Over.w U'.gen.hom).symm
    have : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U'.gen.hom.left A'.A.hom inferInstance A'.isAb.proper
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic (powObj G₀ 8) hS8 hp
  obtain ⟨w, -, hw, -, -, hwL, -⟩ := GlobalTheory.PowE8.hypW_e8LB _ G₀ P₁ W hW
  have hwL' : LBIso Pc.L.L (cubeLB (powObj G₀ 8) ![𝟙 _, w] Pc.L.L) := by rw [hPc]; exact hwL
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V₁) 0 Pc
  have hB' : IsAbelianScheme (thickObj V₁ (maximalIdeal V₁) 0 D'.toPre.P.A) :=
    by
      have h := D'.toPre.P.isAb
      have := h.comm
      have := h.smooth
      have := h.proper
      have := h.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
      · change IsProper (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
      · change GeometricallyConnected (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U'.gt 0) hB'
  have hm : (maximalIdeal V₁ ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) := Ideal.Quotient.field _
  have : Smooth (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)).hom := by
    have := hS8.smooth
    change Smooth (pullback.snd (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0))
    infer_instance
  have : GeometricallyConnected (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)).hom := by
    have := hS8.geomConnected
    change GeometricallyConnected (pullback.snd (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0))
    infer_instance
  have := Q₀.i_hom
  letI := D'.toPre.addX
  haveI := D'.toPre.freeX
  haveI := D'.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) D'.toPre.X
    (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)) P₀.L P₀.c Q₀.i Q₀.i_hom
  haveI := hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective h3 Pc w hwL' P₀
    (IsPullback.of_hasPullback (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0)) hv Q₀.i s
  exact ⟨D'.toPre.X, D'.toPre.addX, D'.toPre.freeX, D'.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

end GlobalTheory.PowE8
end
