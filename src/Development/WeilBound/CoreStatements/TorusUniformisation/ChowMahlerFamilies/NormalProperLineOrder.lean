import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecialFibreClosedSpecialization

section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurvePositivity

theorem change_gen {Ω : Type} [Field Ω] (σ π e f : Ω) (M : ℕ) (hf : f ≠ 0) :
    π / (σ / e) ^ M = π / (σ / f) ^ M * (e / f) ^ M := by
  have hfM : f ^ M ≠ 0 := pow_ne_zero _ hf
  rw [div_pow, div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]
  by_cases hσ : σ ^ M = 0
  · simp [hσ]
  · field_simp

theorem val_one {K : Type} [Field K] (C : Crv.ACurve K) (hw : ∀ i, 0 < C.w i) (c : K) (hc : c ≠ 0)
    (r t : C.I → K) (M : ℕ) (hr : ∀ i, r i ≠ 0) (hfin : {i | C.v i (r i) ≠ 1}.Finite)
    (hd : ∑ᶠ i, (C.w i : ℤ) * (-WithZero.log (C.v i (r i))) = 0)
    (ht : ∀ i, C.v i (t i) ≤ 1) (hct : ∀ i, c = t i * r i ^ M) (i : C.I) : C.v i (t i) = 1 := by
  have ht0 : ∀ j, t j ≠ 0 := fun j h => hc (by rw [hct j, h, zero_mul])
  have hvt : ∀ j, C.v j (t j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (ht0 j)
  have hvr : ∀ j, C.v j (r j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (hr j)
  have hL : ∀ j, WithZero.log (C.v j c) =
      WithZero.log (C.v j (t j)) + (M : ℤ) * WithZero.log (C.v j (r j)) := by
    intro j
    rw [hct j, map_mul, map_pow, WithZero.log_mul (hvt j) (pow_ne_zero _ (hvr j)), WithZero.log_pow]
    simp
  have hle : ∀ j, WithZero.log (C.v j (t j)) ≤ 0 := by
    intro j
    have := (WithZero.log_le_log (hvt j) one_ne_zero).2 (ht j)
    rwa [WithZero.log_one] at this
  set A : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j (t j)) with hA
  set B : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j c) with hB
  set D : C.I → ℤ := fun j => (C.w j : ℤ) * (-WithZero.log (C.v j (r j))) with hD
  have hsB : (Function.support B).Finite := (C.fin c hc).subset (fun j hj => by
    simp only [Function.mem_support, hB] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, mul_zero])
  have hsD : (Function.support D).Finite := hfin.subset (fun j hj => by
    simp only [Function.mem_support, hD] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, neg_zero, mul_zero])
  have hABD : A = fun j => B j + (M : ℤ) * D j := by
    funext j; simp only [hA, hB, hD]; rw [hL j]; ring
  have hsMD : (Function.support fun j => (M : ℤ) * D j).Finite :=
    hsD.subset (Function.support_mul_subset_right _ _)
  have hsA : (Function.support A).Finite := by
    rw [hABD]; exact (hsB.union hsMD).subset (Function.support_add _ _)
  have hsum : ∑ᶠ j, A j = 0 := by
    rw [hABD, finsum_add_distrib hsB hsMD, ← mul_finsum]
    simp only [hB, hD]
    rw [C.prod c hc, hd, mul_zero, add_zero]
  have hnn : ∀ j, 0 ≤ -A j := fun j => by
    simp only [hA]; have := hle j; have := hw j; nlinarith
  have hsA' : (Function.support fun j => -A j).Finite :=
    hsA.subset (fun j hj => by simpa [Function.mem_support] using hj)
  have h1 := single_le_finsum i hsA' hnn
  rw [finsum_neg_distrib, hsum, neg_zero] at h1
  have h2 : WithZero.log (C.v i (t i)) = 0 := by
    have h3 : A i = 0 := by have := hnn i; linarith
    simp only [hA] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (by have := hw i; omega)
    · exact h4
  rw [← WithZero.exp_log (hvt i), h2, WithZero.exp_zero]

end PositivityTheory.Xgn.CurvePositivity

theorem PositivityTheory.Xgn.degree_zero_curve_positive : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (L : Lat ξ Ω) (σ π : Ω) (M : ℕ) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → L.IsVB 1 ⊤ → 0 < M → Γ.HasDeg L 0 → (∀ (p : Cpt ξ) (e : Ω), L.IsGenAt p e → π / (σ / e) ^ M ∈ regAt ξ p) → (∀ e, L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e → unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ (π / (σ / e) ^ M)) → ∀ (i : Γ.C.I) (h : genPt ξ ⤳ centre (Γ.z i)) (e : Ω), L.IsGenAt ⟨centre (Γ.z i), h⟩ e → unitAt ξ ⟨centre (Γ.z i), h⟩ (π / (σ / e) ^ M) := by
  intro X Ω _ ξ O _ s _ _ ϖ L σ π M Γ hξ _ _ hdeg hreg hunit i h e he
  obtain ⟨e0, f, r, he0, hf, hr, hfin, hd⟩ := hdeg
  have hf' : ∀ j, L.IsGenAt ⟨centre (Γ.z j), Γ.z_spec j⟩ (f j) := fun j => (hf j).2
  obtain ⟨c, hc⟩ := ProjectiveLinePlaces.valAt_of_unit Γ.η_spec (hunit e0 he0)
  choose g hg using fun j => hreg _ _ (hf' j)
  let t : ∀ j, (Γ.C.v j).valuationSubring := fun j => (Scheme.stalkClosedPointTo (Γ.z j)).hom (g j)
  have hz : ∀ j, ValAt ξ (Γ.z j) (π / (σ / f j) ^ M) (t j) := fun j => ⟨Γ.z_spec j, g j, hg j, rfl⟩
  have hη : ∀ j, ValAt ξ Γ.η (π / (σ / f j) ^ M) (t j : Γ.κ) := fun j =>
    ProjectiveLinePlaces.valAt_restrict _ (Γ.z_gen j) Γ.η_spec (hz j)
  have hct : ∀ j, (c : Γ.κ) = (t j : Γ.κ) * r j ^ M := fun j => by
    have h2 := CoordModel.valAt_mul (hη j) (ProjectiveLinePlaces.valAt_pow (hr j).2 M)
    rw [← PositivityTheory.Xgn.CurvePositivity.change_gen σ π e0 (f j) M (hf' j).1] at h2
    exact CoordModel.valAt_unique hξ hc h2
  have hv := PositivityTheory.Xgn.CurvePositivity.val_one Γ.C Γ.w_pos c c.ne_zero r (fun j => (t j : Γ.κ)) M
    (fun j => (hr j).1) hfin hd (fun j => (t j).2) hct i
  have ht0 : (t i : Γ.κ) ≠ 0 := fun h0 => by simp [h0] at hv
  have hu : IsUnit (t i) := by
    refine IsUnit.of_mul_eq_one ⟨(t i : Γ.κ)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ ht0))
    change Γ.C.v i _ ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hgu : IsUnit (g i) := (Scheme.isLocalHom_stalkClosedPointTo' (Γ.z i)).map_nonunit (g i) hu
  obtain ⟨u, hu1, hu2⟩ := (CptModel.unitAt_iff ξ _ _).1 (ProjectiveLinePlaces.unitAt_div he (hf' i))
  refine (CptModel.unitAt_iff ξ _ _).2 ⟨g i * u ^ M, hgu.mul (hu1.pow M), ?_⟩
  rw [PositivityTheory.Xgn.CurvePositivity.change_gen σ π e (f i) M (hf' i).1, map_mul, map_pow, hu2]
  exact congrArg (· * (e / f i) ^ M) (hg i)
end

section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ProperZeroNumerical

theorem subset_of_specializes {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] [QuasiSober T]
    {Z V : Set T} (hZ : IsClosed Z) (hc : IsPreconnected Z) (hV : IsOpen V) (hne : (Z ∩ V).Nonempty)
    (hs : ∀ y x : T, y ∈ Z → y ∈ V → y ⤳ x → x ∈ V) : Z ⊆ V := by
  have hcl : IsClosed (Z ∩ V) := by
    obtain ⟨S, hfin, hScl, hSirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
    have e : Z ∩ V = ⋃ t ∈ {t ∈ S | (t ∩ V).Nonempty}, t := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨hx, hxV⟩
        rw [hU] at hx
        obtain ⟨t, ht, hxt⟩ := hx
        exact ⟨t, ⟨ht, x, hxt, hxV⟩, hxt⟩
      · rintro ⟨t, ⟨ht, htV⟩, hxt⟩
        have hsub : t ⊆ Z := by rw [hU]; exact Set.subset_sUnion_of_mem ht
        obtain ⟨y, hy⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
        exact ⟨hsub hxt, hs y x (hsub hy.mem) ((hy.mem_open_set_iff hV).2 htV) (hy.specializes hxt)⟩
    rw [e]
    exact (hfin.subset fun t ht => ht.1).isClosed_biUnion fun t ht => hScl t ht.1
  intro x hx
  by_contra hxV
  obtain ⟨z, hz, hzV, hz'⟩ := hc V (Z ∩ V)ᶜ hV hcl.isOpen_compl
    (fun w hw => by
      by_cases h : w ∈ V
      · exact Or.inl h
      · exact Or.inr fun h' => h h'.2) hne ⟨x, hx, fun h => hxV h.2⟩
  exact hz' ⟨hz, hzV⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unit_mul {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unit_inv {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unit_pow {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

theorem unit_change {L : Lat ξ Ω} {p : Cpt ξ} {σ π e f : Ω} {M : ℕ} (he : L.IsGenAt p e) (hf : L.IsGenAt p f)
    (h : unitAt ξ p (π / (σ / f) ^ M)) : unitAt ξ p (π / (σ / e) ^ M) := by
  rw [CurvePositivity.change_gen σ π e f M hf.1]
  exact unit_mul h (unit_pow (ProjectiveLinePlaces.unitAt_div he hf) M)

theorem exists_local_gen {L : Lat ξ Ω} (h : L.IsVB 1 ⊤) (p : Cpt ξ) :
    ∃ (U : X.Opens) (e : Ω), p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q e := by
  obtain ⟨U, hp, b, -, hb⟩ := h p (Set.mem_univ p)
  refine ⟨U, b 0, hp, fun q hq => ?_⟩
  obtain ⟨hli, hspan⟩ := hb q (Set.mem_univ q) hq
  refine ⟨hli.ne_zero 0, ?_⟩
  rw [hspan]
  congr 1
  ext x
  simp [eq_comm]

end PositivityTheory.Xgn.ProperZeroNumerical

open PositivityTheory.Xgn.ProperZeroNumerical in
theorem PositivityTheory.Xgn.normal_proper_line_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb hnum hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := { }
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, e₀, c₀, he₀, hL₀, hσ₀, hu₀⟩ :=
    exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.1 L σ hvb hgen
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  set π : Ω := algebraMap O Ω ϖ ^ a with hπ
  let Good : Cpt ξ → Prop := fun p => ∃ e, L.IsGenAt p e ∧ unitAt ξ p (π / (σ / e) ^ M)
  let V : Set X := ⋃₀ {W | IsOpen W ∧ ∀ q : Cpt ξ, q.1 ∈ W → Good q}
  have hVo : IsOpen V := isOpen_sUnion fun W hW => hW.1
  have hV : ∀ q : Cpt ξ, q.1 ∈ V ↔ Good q := by
    intro q
    constructor
    · rintro ⟨W, hW, hq⟩
      exact hW.2 q hq
    · rintro ⟨e, he, hu⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      obtain ⟨U', hqU', hU'⟩ := (regAt_unitAt_open X Ω ξ q _).2 (unit_change (hb q hqU) he hu)
      exact ⟨(U : Set X) ∩ U', ⟨U.isOpen.inter U'.isOpen, fun r hr => ⟨b, hb r hr.1, hU' r hr.2⟩⟩, hqU, hqU'⟩
  have hZ : IsClosed (zeroSet ξ (algebraMap O Ω ϖ)) := by
    have e : zeroSet ξ (algebraMap O Ω ϖ) =
        closure {genPt ξ} ∩ s ⁻¹' (PrimeSpectrum.zeroLocus ({ϖ} : Set O)) := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.1 h1,
          Set.singleton_subset_iff.2 (not_not.1 fun h => h2 ((hunit ⟨x, h1⟩ ϖ).2 h))⟩
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.2 h1, fun h =>
          (hunit ⟨x, specializes_iff_mem_closure.2 h1⟩ ϖ).1 h (Set.singleton_subset_iff.1 h2)⟩
    rw [e]
    exact isClosed_closure.inter ((PrimeSpectrum.isClosed_zeroLocus _).preimage s.continuous)
  have hsub : zeroSet ξ (algebraMap O Ω ϖ) ⊆ V := by
    refine subset_of_specializes hZ hconn.2 hVo ⟨p₀.1, ⟨p₀.2, hp₀⟩, (hV p₀).2 ⟨e₀, ⟨he₀, hL₀⟩, ?_⟩⟩ ?_
    · have e1 : σ / e₀ = c₀ := by rw [hσ₀, smul_eq_mul, mul_div_cancel_right₀ _ he₀]
      rw [e1, ← inv_div]
      exact unit_inv hu₀
    · rintro y x ⟨hy, hyn⟩ hyV hyx
      obtain ⟨x', hx', hcl⟩ :=
        (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton ⟨x, subset_closure rfl⟩
      have hxx : x ⤳ x' := specializes_iff_mem_closure.2 hx'
      refine hxx.mem_open hVo ?_
      have hyx' : y ⤳ x' := hyx.trans hxx
      let q : Cpt ξ := ⟨x', hy.trans hyx'⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      refine (hV q).2 ⟨b, hb q hqU, ?_⟩
      by_contra hnu
      obtain ⟨e, he, hue⟩ := (hV ⟨y, hy⟩).1 hyV
      obtain ⟨Γ, i, -, hη, hz⟩ := GlobalTheory.T.special_fibre_closed_specialization X Ω ξ O s ϖ hϖ hinj hs hg ⟨y, hy⟩ q (π / (σ / b) ^ M) hyn hyx' hcl
        (hreg q b (hb q hqU)) (unit_change (hb ⟨y, hy⟩ (hyx'.mem_open U.isOpen hqU)) he hue) hnu
      have hq : q = ⟨centre (Γ.z i), Γ.z_spec i⟩ := Subtype.ext hz.symm
      have hηU : centre Γ.η ∈ U := (Γ.generic_centre_specializes i).mem_open U.isOpen (by rw [hz]; exact hqU)
      apply hnu
      have hbq := hb q hqU
      rw [hq] at hbq ⊢
      exact PositivityTheory.Xgn.degree_zero_curve_positive X Ω ξ O s _ L σ π M Γ hg hvb hM (hnum Γ) hreg
        (fun e' he' => unit_change he' (hb ⟨centre Γ.η, Γ.η_spec⟩ hηU) hη) i (Γ.z_spec i) b hbq
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hu : unitAt ξ p (algebraMap O Ω ϖ)
  · have hp : p ∈ genFibre O ξ := by
      intro o ho
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
      rw [map_mul, map_pow]
      refine unit_mul ((hunit p _).2 fun h => ?_) (unit_pow hu n)
      exact (s p.1).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
    refine ⟨σ, 1, (hgen p hp).1, (hgen p hp).2, (one_smul _ _).symm, ?_⟩
    rw [one_pow, one_div]
    refine unit_inv ⟨zpow_ne_zero a hu.1, ZLat.zpow_mem_regAt hu a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hu _
  · obtain ⟨e, he, hue⟩ := (hV p).1 (hsub ⟨p.2, hu⟩)
    refine ⟨e, σ / e, he.1, he.2, ?_, ?_⟩
    · rw [smul_eq_mul, div_mul_cancel₀ _ he.1]
    · rw [← inv_div]
      exact unit_inv hue
end
