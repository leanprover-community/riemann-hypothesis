import Development.EtaleCohomology.EtaleSheaves.QuotientFieldNonconstantLift
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

section
open Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

variable {X : Type} [TopologicalSpace X]

theorem two_le_dim (A B : IrreducibleCloseds X) (hAB : (A : Set X) ⊂ B) (hB : (B : Set X) ≠ univ)
    [IrreducibleSpace X] : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h1 : A < B := by
    rw [← SetLike.coe_ssubset_coe]; exact hAB
  have h2 : B < T := by
    rw [← SetLike.coe_ssubset_coe]; exact ssubset_univ_iff.mpr hB
  let l : LTSeries (IrreducibleCloseds X) := ⟨2, ![A, B, T], fun i => by
    fin_cases i
    · exact h1
    · exact h2⟩
  have hl : l.length = 2 := rfl
  unfold topologicalKrullDim
  exact Order.le_krullDim_iff.mpr ⟨l, hl⟩

theorem closed_of_ne_univ [IrreducibleSpace X] [T0Space X] (hd : topologicalKrullDim X ≤ 1) (z : X)
    (hz : closure ({z} : Set X) ≠ univ) : IsClosed ({z} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hyz : closure ({y} : Set X) ⊂ closure {z} := by
    refine ⟨closure_minimal (by simpa using hy) isClosed_closure, fun h => hne ?_⟩
    have h1 : z ⤳ y := specializes_iff_mem_closure.mpr hy
    have h2 : y ⤳ z := specializes_iff_mem_closure.mpr (h (subset_closure rfl))
    exact (h1.antisymm h2).eq.symm
  have := two_le_dim ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ hyz hz
  have h3 := this.trans hd
  norm_cast at h3

theorem finite_of_closed [IrreducibleSpace X] [T0Space X] [QuasiSober X] [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) (Z : Set X) (hZ : IsClosed Z) (hne : Z ≠ univ) : Z.Finite := by
  have hpt : ∀ z ∈ Z, IsClosed ({z} : Set X) := fun z hz => closed_of_ne_univ hd z
    (fun h => hne (eq_univ_of_univ_subset (h ▸ closure_minimal (by simpa using hz) hZ)))
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Z)
  have hsub : ∀ S ∈ irreducibleComponents Z, (Subtype.val '' S).Subsingleton := by
    intro S hS
    have hirr : IsIrreducible (Subtype.val '' S) := hS.1.image _ continuous_subtype_val.continuousOn
    obtain ⟨g, hg⟩ := QuasiSober.sober hirr.closure isClosed_closure
    have hgZ : g ∈ Z := closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hZ (hg.mem)
    have : closure (Subtype.val '' S) = {g} := by
      rw [← hg.def, (hpt g hgZ).closure_eq]
    intro a ha b hb
    have ha' := subset_closure ha; have hb' := subset_closure hb
    rw [this] at ha' hb'
    exact ha'.trans hb'.symm
  have : Z = ⋃ S ∈ irreducibleComponents Z, Subtype.val '' S := by
    ext x; constructor
    · intro hx
      have : (⟨x, hx⟩ : Z) ∈ ⋃₀ irreducibleComponents Z := by rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨S, hS, hxS⟩ := this
      exact mem_iUnion₂.mpr ⟨S, hS, ⟨_, hxS, rfl⟩⟩
    · intro hx
      obtain ⟨S, -, y, -, rfl⟩ := mem_iUnion₂.mp hx
      exact y.2
  rw [this]
  exact hfin.biUnion fun S hS => (hsub S hS).finite

end LateralTheory.E.CurveKrullDim
end

section
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
end
end
