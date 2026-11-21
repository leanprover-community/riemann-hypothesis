import Development.EtaleCohomology.EtaleSheaves.LeafGlueIsProperPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

set_option backward.isDefEq.respectTransparency false in
theorem sep_of_cover {X S : Scheme.{0}} (f : X ⟶ S) (U : X.OpenCover)
    (H : ∀ i j, IsClosedImmersion (pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f
      (by simp) (by simp))) : IsSeparated f := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight U U f f)
  rintro ⟨i, j⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv]
  have e : (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv ≫
      (Scheme.Pullback.openCoverOfLeftRight U U f f).pullbackHom (pullback.diagonal f) (i, j) =
      pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp only [Scheme.Cover.pullbackHom, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
    · exact pullbackDiagonalMapIdIso_inv_snd_fst (U.f i) (U.f j) f
    · exact pullbackDiagonalMapIdIso_inv_snd_snd (U.f i) (U.f j) f
  rw [e]; exact H i j

theorem closed_of_pb {X S W P Q : Scheme.{0}} (f : X ⟶ S) (ia : P ⟶ X) (ib : Q ⟶ X) (pa : W ⟶ P)
    (pb : W ⟶ Q) (hp : IsPullback pa pb ia ib) (ga : P ⟶ S) (gb : Q ⟶ S) (hga : ia ≫ f = ga)
    (hgb : ib ≫ f = gb) (w : pa ≫ ga = pb ≫ gb)
    (hc : IsClosedImmersion (pullback.lift pa pb w)) :
    IsClosedImmersion (pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp)) := by
  subst hga hgb
  have e : pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift pa pb w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_inv_snd]
  rw [e]; infer_instance

def LeafGluePullback : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsPullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)).toRingHom))
    G.iA G.iB

theorem spec_w {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L) (hA : A ≤ D) (hB : B ≤ D) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hA).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]; congr 1

def LeafSpecGenClosed : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
  (hA : A ≤ D) (hB : B ≤ D), D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) →
  IsClosedImmersion (pullback.lift _ _ (spec_w A B D hA hB))

theorem dr_le {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) (hu : u⁻¹ ∈ B) :
    Dr Ω A u ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr hu))

theorem LeafGlueSep_of (hP : LeafGluePullback) (hC : LeafSpecGenClosed) :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hD := dr_le A B u h.2.2.1
  apply sep_of_cover G.c0 (LateralTheory.E.LeafGlueIsProperPf.cov G)
  intro i j
  cases i <;> cases j
  · exact closed_of_pb G.c0 G.iB G.iB (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iB) _ _ G.hcB G.hcB (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω B))))))
  · exact closed_of_pb G.c0 G.iB G.iA _ _ (hP Ω L A B u h G).flip _ _ G.hcB G.hcA _
      (hC Ω L B A _ _ _ (by rw [Set.union_comm]; exact hD))
  · exact closed_of_pb G.c0 G.iA G.iB _ _ (hP Ω L A B u h G) _ _ G.hcA G.hcB _ (hC Ω L A B _ _ _ hD)
  · exact closed_of_pb G.c0 G.iA G.iA (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iA) _ _ G.hcA G.hcA (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω A))))))

end LateralTheory.E.GluedCurveChartOverlaps
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem prod_surj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hA : A ≤ D) (hB : B ≤ D) (hD : D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B)) :
    Function.Surjective (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) := by
  intro x
  have hx : (x : L) ∈ (Algebra.TensorProduct.productMap A.val B.val).range := by
    rw [Algebra.TensorProduct.productMap_range, A.range_val, B.range_val]
    have := hD x.2
    rwa [Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq] at this
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  rw [← hy]
  have e : D.val.comp (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) =
      Algebra.TensorProduct.productMap A.val B.val := by
    ext <;> rfl
  exact congrArg (fun φ : _ →ₐ[Ω] L => φ y) e

theorem spec_subalgebra_pullback_lift_is_closed_immersion : LeafSpecGenClosed := by
  intro Ω L _ _ _ A B D hA hB hD
  let φ := Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)
  have e : pullback.lift _ _ (spec_w A B D hA hB) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso Ω A B).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
  rw [e]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (prod_surj A B D hA hB hD)
  infer_instance

end LateralTheory.E.GluedCurveChartOverlaps
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem mem_adj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B : Subalgebra Ω L) (u : L) (hu : u ≠ 0)
    (huB : u⁻¹ ∈ B) (d : L) (hd : d ∈ Algebra.adjoin Ω ((B : Set L) ∪ {u})) : ∃ n : ℕ, d * u⁻¹ ^ n ∈ B := by
  induction hd using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hu]; exact B.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * u⁻¹ ^ m + (y * u⁻¹ ^ m) * u⁻¹ ^ n := by ring
    rw [this]
    exact B.add_mem (B.mul_mem hn (B.pow_mem huB _)) (B.mul_mem hm (B.pow_mem huB _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * (y * u⁻¹ ^ m) := by ring
    rw [this]; exact B.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B D : Subalgebra Ω L) (hB : B ≤ D) (u : L)
    (hu : u ≠ 0) (huB : u⁻¹ ∈ B) (huD : u ∈ D) (hD : D ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u})) :
    letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
    IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D := by
  letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap B D ((⟨u⁻¹, huB⟩ : B) ^ n))
    rw [map_pow]
    refine IsUnit.pow n ?_
    exact ⟨⟨algebraMap B D ⟨u⁻¹, huB⟩, ⟨u, huD⟩, Subtype.ext (inv_mul_cancel₀ hu),
      Subtype.ext (mul_inv_cancel₀ hu)⟩, rfl⟩
  · intro d
    obtain ⟨n, hn⟩ := mem_adj B u hu huB d (hD d.2)
    refine ⟨(⟨d * u⁻¹ ^ n, hn⟩, ⟨_, n, rfl⟩), Subtype.ext ?_⟩
    show d * u⁻¹ ^ n = (d : L) * (u⁻¹ ^ n)
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : L) = (y : L) := by
      have h2 := congrArg (fun z : D => (z : L)) hxy
      exact h2
    simp [Subtype.ext this]

set_option backward.isDefEq.respectTransparency false in
theorem glued_curve_chart_overlap_is_pullback : LeafGluePullback := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hadj := h.2.2.2.2.2.2.2.2.2.2.2.1
  have huD : u ∈ Dr Ω A u := Algebra.subset_adjoin (Or.inl h.2.1)
  have hD : Dr Ω A u ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u}) := hadj.le
  haveI hjB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom)) := by
    letI : Algebra B (Dr Ω A u) := (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom.toAlgebra
    haveI := away B (Dr Ω A u) (le_Dr_B A B u hadj) u h.1 h.2.2.1 huD hD
    exact IsOpenImmersion.of_isLocalization (S := Dr Ω A u) (⟨u⁻¹, h.2.2.1⟩ : B)
  refine IsOpenImmersion.isPullback _ _ _ _ G.agree.symm ?_
  ext x
  show G.iB.base x ∈ Set.range G.iA.base ↔ x ∈ Set.range _
  constructor
  · intro hx
    have hx' : G.iB.base x ∈ Set.range G.iA.base ∩ Set.range G.iB.base := ⟨hx, x, rfl⟩
    rw [G.inter, G.agree] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, G.iB.isOpenEmbedding.injective ?_⟩
    rw [← hy]; rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom)).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.agree]; rfl

end LateralTheory.E.GluedCurveChartOverlaps

namespace LateralTheory.E.GluedCurveSeparated

theorem LeafGlueSep_of : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep :=
  LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback
    LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion

end LateralTheory.E.GluedCurveSeparated
end
end
