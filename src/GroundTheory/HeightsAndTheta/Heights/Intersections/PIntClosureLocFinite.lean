module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StIntClosureLocFinite
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StRelAlgClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem IntClosureLocFinite.proof (h : RelAlgClosureFinite.Statement) :
    IntClosureLocFinite.Statement := by
  classical
  intro F L _ _ φ S hS A T hDA hloc
  let : Algebra A L := (φ.comp A.subtype).toAlgebra

  let D : Subring F := Subring.closure (T : Set F)
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.equiv ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T))
      (Subring.closureEquivAdjoinInt _).symm
  let : Algebra D L := (φ.comp D.subtype).toAlgebra
  let : Algebra D A := (Subring.inclusion hDA).toAlgebra
  have : IsScalarTower D A L := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let K := FractionRing D
  have hinj : Function.Injective (φ.comp D.subtype) := φ.injective.comp Subtype.val_injective
  let : Algebra K L := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower D K L :=
    IsScalarTower.of_algebraMap_eq fun d => (IsFractionRing.lift_algebraMap hinj d).symm
  have hKS : IntermediateField.adjoin K (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subfield.closure (S : Set L) := hS ▸ Subfield.mem_top x
    exact (Subfield.closure_le (t := (IntermediateField.adjoin K (S : Set L)).toSubfield)).mpr
      (IntermediateField.subset_adjoin K _) hx

  let M := algebraicClosure K L
  have : FiniteDimensional K M := h K L S hKS
  have : IsScalarTower D M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : Module.Finite D (integralClosure D M) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full D K M
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.image fun g : integralClosure D M => ((g : M) : L), fun x hx => ?_⟩

  let U : Submonoid D := (IsUnit.submonoid A).comap (Subring.inclusion hDA)
  have : IsLocalization U A := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {d₁ d₂} hd => ⟨1, ?_⟩⟩
    · obtain ⟨b, hb, c, hc, hc0, hcA, hzc⟩ := hloc z z.2
      have hunit : IsUnit (Subring.inclusion hDA ⟨c, hc⟩) :=
        IsUnit.of_mul_eq_one (⟨c⁻¹, hcA⟩ : A) (Subtype.ext (mul_inv_cancel₀ hc0))
      exact ⟨(⟨b, hb⟩, ⟨⟨c, hc⟩, hunit⟩), Subtype.ext hzc⟩
    · rw [Subring.inclusion_injective hDA hd]
  obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := A) U x hx

  obtain ⟨y, hy⟩ : ∃ y : L, y = (⟨m, hm⟩ : U) • x := ⟨_, rfl⟩
  rw [← hy] at hmx
  have hyK : IsIntegral K y := hmx.tower_top
  let yM : M := ⟨y, hyK⟩
  have hyMint : IsIntegral D yM := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom D M L) (fun a b hab => Subtype.ext hab)]
    exact hmx
  have hyspan : (⟨yM, hyMint⟩ : integralClosure D M) ∈ Submodule.span D (s : Set _) :=
    hs ▸ Submodule.mem_top
  let f : integralClosure D M →ₗ[D] L :=
    (IsScalarTower.toAlgHom D M L).toLinearMap ∘ₗ (integralClosure D M).val.toLinearMap
  have hyD : y ∈ Submodule.span D ((s.image fun g : integralClosure D M => ((g : M) : L)) : Set L) := by
    have hmap := Submodule.mem_map_of_mem (f := f) hyspan
    rw [Submodule.map_span] at hmap
    rw [Finset.coe_image]
    exact hmap
  have hyA := Submodule.span_subset_span D A _ hyD

  have hu : IsUnit (algebraMap D A m) := hm
  have hyu : y = (hu.unit : A) • x := by
    rw [hy, Submonoid.smul_def, IsUnit.unit_spec, algebraMap_smul]
  have hx' : x = ((hu.unit⁻¹ : Aˣ) : A) • y := by
    rw [hyu, smul_smul, Units.inv_mul, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ hyA

end GroundTheory.Heights₂.Heights.Inter
