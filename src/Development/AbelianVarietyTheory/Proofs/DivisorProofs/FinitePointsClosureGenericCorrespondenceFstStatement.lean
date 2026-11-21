import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackKernelOfKernelPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPointStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem finite_specialisations_of_finite_open {R : Type} [CommRing R] {X : Scheme.{0}} (sX : X ⟶ Sp R)
    [IsSeparated sX] (U : X.Opens) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ X) (gs : Y₀ ⟶ U.toScheme)
    (hgs : gs ≫ U.ι = s₀) [IsFinite gs] (u : X) (hu : u ∈ U) :
    {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K)
      (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  have hF : (s₀.base ⁻¹' {u}).Finite := by
    refine (gs.finite_preimage_singleton (⟨u, hu⟩ : U)).subset fun y hy => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hgs, hy]
    rfl
  refine (hF.image t₀.base).subset ?_
  rintro z ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, h3, h4⟩
  have hrange : Set.range y'.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := V) w).map y'.continuous).mem_open U.isOpen (h3 ▸ hu)
  have hy''f : IsOpenImmersion.lift U.ι y' hrange ≫ U.ι = y' := IsOpenImmersion.lift_fac _ _ _
  have hE : ValuativeCriterion.Existence gs :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gs) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gs).1
  have hw : x ≫ gs = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ IsOpenImmersion.lift U.ι y' hrange := by
    rw [← cancel_mono U.ι, Category.assoc, hgs, Category.assoc, hy''f]
    exact h1.symm
  obtain ⟨⟨l, hl1, hl2⟩⟩ :=
    (hE { R := V, K := K, i₁ := x, i₂ := IsOpenImmersion.lift U.ι y' hrange, commSq := ⟨hw⟩ }).exists_lift
  have hl1' : spMap (algebraMap V K) ≫ l = x := hl1
  have hl2' : l ≫ gs = IsOpenImmersion.lift U.ι y' hrange := hl2
  have : IsDominant (spMap (algebraMap V K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)).le.trans bot_le)⟩
  have hlz : l ≫ t₀ = z' := by
    refine ext_of_isDominant_of_isSeparated (sX ≫ spMap (algebraMap ℤ R)) ?_ (spMap (algebraMap V K)) ?_
    · exact specZIsTerminal.hom_ext _ _
    · rw [reassoc_of% hl1', h2]
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hc : (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) = y' (IsLocalRing.closedPoint V) := by
      rw [reassoc_of% hl2', hy''f]
    calc s₀ (l (IsLocalRing.closedPoint V)) = (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) := by
          rw [hgs]; first | rfl | simp
      _ = u := hc.trans h3
  · rw [← h4, ← hlz]
    first | rfl | simp

theorem isSeparated_structure_morphism_model {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have := isProper_str R n
  rw [← e]
  infer_instance

theorem finite_specialisations_of_finite_source : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ b N M Y₀ s₀ t₀ gs hgs hfin u hu
  have := isSeparated_structure_morphism_model M
  exact finite_specialisations_of_finite_open M.s _ Y₀ s₀ t₀ gs hgs u hu

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_section_over_ordinary_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (exact GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem exists_geomPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (y : Sp V ⟶ X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : X.residueField (y (IsLocalRing.closedPoint V)) →+* k)
      (π : Sp k ⟶ Sp V), π ≫ y = spMap σ ≫ X.fromSpecResidueField (y (IsLocalRing.closedPoint V)) ∧
      ∀ q, π q = IsLocalRing.closedPoint V := by
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  haveI : IsLocalHom g₀ := RingHom.isLocalHom_comp _ _
  have hπ : ∀ q, spMap g₀ q = IsLocalRing.closedPoint V := by
    intro q
    have hq : q = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hq]
    exact IsLocalRing.comap_closedPoint g₀
  obtain ⟨⟨x, σ⟩, h⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective (spMap g₀ ≫ y)
  rw [Scheme.SpecToEquivOfField_symm_apply] at h
  have hx : x = y (IsLocalRing.closedPoint V) := by
    let q : Sp k := IsLocalRing.closedPoint k
    have e : (Spec.map σ ≫ X.fromSpecResidueField x) q = (spMap g₀ ≫ y) q := congrArg (fun g : Sp k ⟶ X => g q) h
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hπ, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hx
  exact ⟨k, inferInstance, inferInstance, σ.hom, spMap g₀, h.symm, hπ⟩

theorem exists_isogTarget_of_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  rintro p _ D R _ b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z ⟨V, K, _, _, _, _, _, _, y, z', x, hxy, hxz, rfl, rfl⟩
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  have hxz' : kF ≫ z' = x' ≫ t₀ := by rw [hk, Category.assoc, hxz]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMap.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ →
      ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x'
    o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', ψ, hψV, -⟩ := IsogDVR.exists_isPIsog_extend_dvr p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMap.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMap.comp n₀' mt₀⟩⟩
  haveI : IsSeparated M.s := by
    obtain ⟨n, i, hi, -, e⟩ := M.qproj
    have : IsSeparated (PSpace.str R n) := by
      unfold PSpace.str
      infer_instance
    rw [← e]
    infer_instance
  haveI : M.X.IsSeparated := ⟨by rw [← terminal.comp_from M.s]; infer_instance⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsDominant kF := inferInstanceAs (IsDominant (spMap (algebraMap V (FractionRing V))))
  have hzz : z = z' := ext_of_isDominant kF (by rw [e1, ← e2, hxz'])
  subst hzz
  obtain ⟨k, _, _, σ, π, hπ, hπc⟩ := exists_geomPt_closedPoint V M.X y
  refine ⟨k, inferInstance, inferInstance, σ, π ≫ z, fun q => by rw [Scheme.Hom.comp_apply, hπc], ?_⟩
  rw [← hπ]
  obtain ⟨o₁, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o
  obtain ⟨o₁', ⟨n'⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o'
  obtain ⟨ψ₁, hψ₁, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp V) (Sp k) (y ≫ M.s) (π ≫ (y ≫ M.s)) π
    o o' o₁ o₁' n n' ψ hψV
  refine ⟨by rw [Category.assoc, Category.assoc, hz], ?_⟩
  rw [Category.assoc]
  exact ⟨o₁, o₁', ψ₁, ⟨n.comp my⟩, ⟨n'.comp mz⟩, hψ₁⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pIsogenyTarget_of_dvr_specialisation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr) | (exact GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPIsogenyTargetOfPointPair_field_extension : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (c : ℕ) (k L : Type) [Field k] [Field L] (j : k →+* L) (ξ ζ : Sp k ⟶ M.X), CorrQF.IsogTarget M c ξ ζ → CorrQF.IsogTarget M c (spMap j ≫ ξ) (spMap j ≫ ζ) := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap) | (exact GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES
open GlobalTheory.UPel.HT.ES.CorrQF

theorem closure_points_finite_fst : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ u : M.X, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw huw hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hψ htj u
  by_cases hu : u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  · exact GlobalTheory.T.finite_section_over_ordinary_locus p D R b N M Y₀ s₀ t₀ gs hgs hfs u hu
  · set Z := {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} with hZ
    have key := fun (z : Z) => GlobalTheory.T.exists_pIsogenyTarget_of_dvr_specialisation p D R b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z.1 z.2
    choose k hk _ σ ζ hζ hT using key
    obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField u) Z k σ
    refine (Set.Finite.biUnion (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm c M u hu L h) fun ζ' _ => Set.finite_range (fun q : Sp L => ζ' q)).subset ?_
    intro z hz
    have h1 := GlobalTheory.T.isPIsogenyTargetOfPointPair_field_extension p D R b N M c (k ⟨z, hz⟩) L (g ⟨z, hz⟩) _ _ (hT ⟨z, hz⟩)
    have e : spMap (g ⟨z, hz⟩) ≫ spMap (σ ⟨z, hz⟩) ≫ M.X.fromSpecResidueField u = spMap h ≫ M.X.fromSpecResidueField u := by
      rw [← Category.assoc, ← hg ⟨z, hz⟩]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← Category.assoc] at h1
    simp only [Set.mem_iUnion, Set.mem_range]
    refine ⟨spMap (g ⟨z, hz⟩) ≫ ζ ⟨z, hz⟩, ?_, Classical.arbitrary _, ?_⟩
    · simpa [e] using h1
    · rw [Scheme.Hom.comp_apply, hζ ⟨z, hz⟩ _]

end GlobalTheory.UPel.HT.ES
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_closure_genericCorrespondence_fst : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ u : M.X, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.closure_points_finite_fst) | (exact GlobalTheory.UPel.HT.ES.closure_points_finite_fst) | (intros; apply GlobalTheory.UPel.HT.ES.closure_points_finite_fst <;> assumption)
end
