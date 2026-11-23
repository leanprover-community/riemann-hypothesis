module

public import Development.EtaleCohomology.EtaleSheaves.QuotientFieldNonconstantLift
public import Development.EtaleCohomology.EtaleSheaves.CurveKrullDimTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

def LeafCurveNotPoint : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsCurve c → ¬ Subsingleton C

theorem dim_le_one (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) {Ω : Type} [Field Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : SmoothOfRelativeDimension 1 c) : topologicalKrullDim C ≤ 1 := by
  let e : (⊥ : Subalgebra Ω Ω) ≃+* Ω := (Algebra.botEquiv Ω Ω).toRingEquiv
  let φ : Sp Ω ⟶ Sp (⊥ : Subalgebra Ω Ω) := Spec.map e.toCommRingCatIso.hom
  have : IsIso φ := inferInstance
  have : SmoothOfRelativeDimension 1 (c ≫ φ) := inferInstanceAs (SmoothOfRelativeDimension (1 + 0) (c ≫ φ))
  have h := hD Ω Ω (⊥ : Subalgebra Ω Ω) Subalgebra.fg_bot (c ≫ φ) this
  rwa [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field, zero_add] at h

theorem LeafCurveSmall_of_cut (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) (hP : LeafCurveNotPoint) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall := by
  intro Ω _ _ C c hc
  obtain ⟨hI, hPr, hS⟩ := id hc
  have : LocallyOfFiniteType c := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : CompactSpace C := by
    have : QuasiCompact c := inferInstance
    exact (quasiCompact_iff_compactSpace c).mp this
  have : IsNoetherian C := by constructor
  have : NoetherianSpace C := inferInstance
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  have hd := dim_le_one hD c hS
  refine ⟨fun hfin => hP Ω c hc ?_, fun Z hZ hinf => ?_⟩
  · have hcp : closedPoints C = univ := by
      have : IsClosed (closedPoints C) := by
        have : closedPoints C = ⋃ x ∈ (hfin.subset (subset_univ (closedPoints C))).toFinset, {x} := by
          ext; simp
        rw [this]; exact isClosed_biUnion_finset fun x hx => by simpa using hx
      rw [← this.closure_eq]; exact closure_closedPoints
    have hη : IsClosed ({genericPoint C} : Set C) := by
      rw [← mem_closedPoints_iff, hcp]; trivial
    have : ({genericPoint C} : Set C) = univ := by
      rw [← hη.closure_eq]; exact (genericPoint_spec C).def
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({genericPoint C} : Set C) := this ▸ mem_univ a
    have hb : b ∈ ({genericPoint C} : Set C) := this ▸ mem_univ b
    exact ha.trans hb.symm
  · by_contra hne
    exact hinf (finite_of_closed hd Z hZ hne)

theorem curveNotPoint : LeafCurveNotPoint := by
  intro Ω _ _ C c hc hsub
  obtain ⟨hI, hPr, hS⟩ := id hc
  obtain ⟨x⟩ : Nonempty C := inferInstance
  have : IsAffine C := inferInstance
  let _ : Field Γ(C, ⊤) := (isField_of_isIntegral_of_subsingleton C).toField
  have hft : (c.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω))
  let φ : Ω →+* Γ(C, ⊤) := (c.appTop).hom.comp ι.inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso ι.inv).2)
  let _ : Algebra Ω Γ(C, ⊤) := φ.toAlgebra
  have : Algebra.FiniteType Ω Γ(C, ⊤) := hφ
  have : Module.Finite Ω Γ(C, ⊤) := finite_of_finite_type_of_isJacobsonRing Ω Γ(C, ⊤)
  have hb : Function.Bijective φ := IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hb2 : Function.Bijective (c.appTop).hom := by
    have : (c.appTop).hom = φ.comp ι.hom.hom := by
      ext a; simp [φ]
    rw [this]; exact hb.comp (ConcreteCategory.bijective_of_isIso ι.hom)
  have : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hb2
  have : IsIso c := by
    have h := Scheme.isoSpec_hom_naturality c
    have : c = C.isoSpec.hom ≫ Spec.map c.appTop ≫ (Sp Ω).isoSpec.inv := by
      rw [reassoc_of% h]; simp
    rw [this]; infer_instance
  have h0 : SmoothOfRelativeDimension 0 c := inferInstance
  exact absurd (ReciprocityTheory.ChartRestriction.G.H1.dim_unique c hS h0 x) (by norm_num)

theorem LeafCurveSmall_of (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall :=
  LeafCurveSmall_of_cut hD curveNotPoint

end LateralTheory.E.CurveKrullDim
