import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingCriterion
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.CartierDual
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityPlace
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyTransfer

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

attribute [local instance 2000] Rep.hV2

section FixedVector

variable {W : Type u} [Group W]

theorem exists_ne_zero_forall_ρ_eq (N : Rep.{u} (ULift.{u} ℤ) W) [Finite N] [Nontrivial N]
    (h2 : ∀ m : N, 2 • m = 0) (hN : ∀ w : W, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) :
    ∃ m : N, m ≠ 0 ∧ ∀ w : W, N.ρ w m = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup (N →ₗ[ULift.{u} ℤ] N)ˣ := N.ρ.asGroupHom.range
  have hR : IsPGroup 2 R := by
    rintro ⟨x, w, rfl⟩
    obtain ⟨k, hk⟩ := hN w
    refine ⟨k, Subtype.ext (Units.ext ?_)⟩
    change ((N.ρ.asGroupHom w ^ 2 ^ k : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) = 1
    rw [← map_pow, Representation.asGroupHom_apply, hk]
  have hcard := hR.card_modEq_card_fixedPoints N
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : N)
  have hord : addOrderOf m₀ = 2 :=
    addOrderOf_eq_prime (h2 m₀) hm₀
  have h2N : 2 ∣ Nat.card N := hord ▸ addOrderOf_dvd_natCard m₀
  have h2F : 2 ∣ Nat.card (MulAction.fixedPoints R N) := (hcard.dvd_iff (dvd_refl 2)).1 h2N
  have h0 : (0 : N) ∈ MulAction.fixedPoints R N := fun r => by
    change ((r : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) 0 = 0
    exact map_zero _
  have hF : Finite (MulAction.fixedPoints R N) := Subtype.finite
  have hlt : 1 < Nat.card (MulAction.fixedPoints R N) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints R N) :=
      Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, hF⟩
    obtain ⟨c, hc⟩ := h2F
    omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Finite.one_lt_card_iff_nontrivial.1 hlt |>.exists_pair_ne
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_or, not_not] at h
    exact hab (Subtype.ext (h.1.trans h.2.symm))
  have key : ∀ c ∈ MulAction.fixedPoints R N, ∀ w : W, N.ρ w c = c := fun c hc w =>
    hc ⟨N.ρ.asGroupHom w, w, rfl⟩
  rcases hne with h | h
  · exact ⟨a, h, key a ha⟩
  · exact ⟨b, h, key b hb⟩

end FixedVector

section ZModTwo

variable {W : Type u} [Group W]

def zmodTwoAddHom {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) : ZMod 2 →+ N :=
  ZMod.lift 2 ⟨zmultiplesHom N m, by
    change ((2 : ℕ) : ℤ) • m = 0
    rw [natCast_zsmul]
    exact hm⟩

theorem zmodTwoAddHom_intCast {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) (k : ℤ) :
    zmodTwoAddHom m hm (k : ZMod 2) = k • m :=
  ZMod.lift_coe _ _ k

theorem zmodTwoAddHom_one {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) :
    zmodTwoAddHom m hm 1 = m := by
  have h := zmodTwoAddHom_intCast m hm 1
  rwa [Int.cast_one, one_zsmul] at h

theorem zmodTwoAddHom_injective {N : Type*} [AddCommGroup N] {m : N} (hm : 2 • m = 0)
    (hm0 : m ≠ 0) : Function.Injective (zmodTwoAddHom m hm) :=
  (injective_iff_map_eq_zero _).2 fun a ha => by
    fin_cases a
    · rfl
    · exact absurd ((zmodTwoAddHom_one m hm).symm.trans ha) hm0

def zmodTwoHom (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0) (hfix : ∀ w : W, N.ρ w m = m) :
    zmodRep.{u} W 2 ⟶ N :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} W 2) N).symm
    ((zmodTwoAddHom m hm).comp (AddEquiv.ulift : ULift.{u} (ZMod 2) ≃+ ZMod 2).toAddMonoidHom),
    fun w => by
      refine LinearMap.ext fun a => ?_
      obtain ⟨a⟩ := a
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
      change zmodTwoAddHom m hm (k : ZMod 2) = N.ρ w (zmodTwoAddHom m hm (k : ZMod 2))
      rw [zmodTwoAddHom_intCast, map_zsmul, hfix]⟩

theorem zmodTwoHom_hom_apply (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0)
    (hfix : ∀ w : W, N.ρ w m = m) (a : zmodRep.{u} W 2) :
    (zmodTwoHom N m hm hfix).hom a = zmodTwoAddHom m hm (ULift.down a) :=
  rfl

end ZModTwo

instance isDiscreteRep_zmodRep {W : Type u} [Group W] [TopologicalSpace W] (n : ℕ) :
    IsDiscreteRep (zmodRep.{u} W n) :=
  isDiscreteRep_of_isTrivial (zmodRep.{u} W n)

section Tate

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

instance isDiscreteRep_coind_zmodRep_openSubgroup (W : OpenSubgroup G) (n : ℕ) :
    IsDiscreteRep (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n)) :=
  isDiscreteRep_coind W _

omit [CompactSpace G] in

theorem eq_zero_tateCompactCohomologyRes_of_subsingleton {k : Type u} [CommRing k]
    {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [Subsingleton A] (n : ℕ)
    (hB : ∀ x : tateCompactCohomologyRes φ ψ B n, x = 0) (x : tateCompactCohomologyRes φ ψ A n) :
    x = 0 :=
  eq_zero_tateCompactCohomologyRes_of_retract φ ψ (0 : A ⟶ B) 0
    (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => Subsingleton.elim _ _)))
    n hB x

theorem eq_zero_tateCompactCohomologyRes_coind_of_two_nsmul (n : ℕ) (W : OpenSubgroup G)
    (hW : ∀ x : tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n, x = 0) :
    ∀ (d : ℕ) (N : Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) [IsDiscreteRep N] [Finite N],
      Nat.card N ≤ d → (∀ m : N, 2 • m = 0) → (∀ w, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) →
      ∀ x : tateCompactCohomologyRes φ ψ (Rep.coind (W : Subgroup G).subtype N) n, x = 0 := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hd
    have := Nat.card_pos (α := N)
    omega
  | succ d ih =>
    intro N _ _ hd h2 hN x
    by_cases hsub : Subsingleton N
    · have : Subsingleton (Rep.coind (W : Subgroup G).subtype N) :=
        ⟨fun a b => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩
      exact eq_zero_tateCompactCohomologyRes_of_subsingleton φ ψ n hW x
    · rw [not_subsingleton_iff_nontrivial] at hsub
      obtain ⟨m, hm0, hfix⟩ := exists_ne_zero_forall_ρ_eq N h2 hN
      let f := zmodTwoHom N m (h2 m) hfix
      let T : Submodule (ULift.{u} ℤ) N := LinearMap.range f.hom.toLinearMap
      have hT : ∀ w, T ≤ T.comap (N.ρ w) := by
        rintro w _ ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        change f.hom a = N.ρ w (f.hom a)
        rw [zmodTwoHom_hom_apply]
        obtain ⟨b⟩ := a
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective b
        change zmodTwoAddHom m (h2 m) (k : ZMod 2) = N.ρ w (zmodTwoAddHom m (h2 m) (k : ZMod 2))
        rw [zmodTwoAddHom_intCast, map_zsmul, hfix]
      have hfinj : Function.Injective f.hom := fun a b hab =>
        ULift.ext _ _ (zmodTwoAddHom_injective (h2 m) hm0 hab)
      let S : ShortComplex (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) :=
        ShortComplex.mk f (Rep.mkQ N T hT) (by
          apply Rep.hom_ext
          apply DFunLike.ext
          intro a
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩)
      have hS : S.ShortExact := by
        refine { exact := ?_, mono_f := (Rep.mono_iff_injective _).2 hfinj, epi_g := ?_ }
        · rw [← ShortComplex.exact_map_iff_of_faithful _
            (forget₂ (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) (ModuleCat.{u} (ULift.{u} ℤ))),
            ShortComplex.moduleCat_exact_iff]
          intro a ha
          change Submodule.Quotient.mk (p := T) a = 0 at ha
          obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 ha
          exact ⟨b, hb⟩
        · refine (Rep.epi_iff_surjective _).2 fun y => ?_
          obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
          exact ⟨a, rfl⟩
      have hCS := shortExact_coindShortComplexOf (W : Subgroup G) hS
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₁ := isDiscreteRep_coind W _
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₂ := isDiscreteRep_coind W _
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₃ := isDiscreteRep_coind W _
      have : Finite (N ⧸ T) := Finite.of_surjective _ (Submodule.mkQ_surjective T)
      have hcardT : 2 ≤ Nat.card T := by
        have h0 : (0 : N) ∈ T := T.zero_mem
        have hm : m ∈ T := ⟨ULift.up 1, by
          rw [LinearMap.coe_mk]
          exact (zmodTwoHom_hom_apply N m (h2 m) hfix _).trans (zmodTwoAddHom_one m (h2 m))⟩
        have : Finite T := Subtype.finite
        exact Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨0, h0⟩, ⟨m, hm⟩,
          fun h => hm0 (congrArg Subtype.val h).symm⟩⟩
      have hcardQ : Nat.card (N ⧸ T) ≤ d := by
        have hc := Submodule.card_eq_card_quotient_mul_card T
        have hpos : 0 < Nat.card (N ⧸ T) := Nat.card_pos
        nlinarith
      refine eq_zero_tateCompactCohomologyRes_of_shortExact φ ψ hCS n hW ?_ x
      refine ih (N.quotient T hT) hcardQ ?_ ?_
      · intro y
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
        exact (map_nsmul T.mkQ 2 a).symm.trans ((congrArg T.mkQ (h2 a)).trans (map_zero _))
      · intro w
        obtain ⟨k, hk⟩ := hN w
        refine ⟨k, DFunLike.ext _ _ fun y => ?_⟩
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
        change Submodule.Quotient.mk (p := T) (N.ρ (w ^ 2 ^ k) a) = Submodule.Quotient.mk a
        rw [hk]
        rfl

theorem eq_zero_tateCompactCohomologyRes_of_two_nsmul (n : ℕ)
    (hW : ∀ W : OpenSubgroup G, ∀ x : tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n, x = 0)
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (h2 : ∀ m : M, 2 • m = 0)
    (x : tateCompactCohomologyRes φ ψ M n) : x = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Subgroup G := ⨅ m : M, stabilizer M.ρ m
  have hU : IsOpen (U : Set G) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    rw [Subgroup.coe_iInf]
    exact Filter.iInter_mem.2 fun m => (isOpen_stabilizer M m).mem_nhds (one_mem _)
  let K₀ : Subgroup G := M.ρ.asGroupHom.ker
  have hUK : U ≤ K₀ := fun g hg => by
    refine (MonoidHom.mem_ker).2 (Units.ext ?_)
    rw [Representation.asGroupHom_apply]
    exact LinearMap.ext fun m => (Subgroup.mem_iInf.1 hg m : M.ρ g m = m)
  let K : OpenSubgroup G := ⟨K₀, Subgroup.isOpen_mono hUK hU⟩
  have : K₀.FiniteIndex := finiteIndex_openSubgroup K
  have : Finite (G ⧸ K₀) := Subgroup.finite_quotient_of_finiteIndex
  let P : Sylow 2 (G ⧸ K₀) := Classical.arbitrary _
  let W : OpenSubgroup G := ⟨(P : Subgroup (G ⧸ K₀)).comap (QuotientGroup.mk' K₀),
    Subgroup.isOpen_mono (fun g hg => by
      change QuotientGroup.mk' K₀ g ∈ (P : Subgroup (G ⧸ K₀))
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
      exact one_mem _) (Subgroup.isOpen_mono hUK hU)⟩
  have hidx : (W : Subgroup G).index = (P : Subgroup (G ⧸ K₀)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K₀)
  have : (P : Subgroup (G ⧸ K₀)).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hodd : ¬ 2 ∣ (W : Subgroup G).index := hidx ▸ Sylow.not_dvd_index P
  have : (W : Subgroup G).FiniteIndex := finiteIndex_openSubgroup W
  have : IsDiscreteRep (Rep.coind (W : Subgroup G).subtype (Rep.res (W : Subgroup G).subtype M)) :=
    isDiscreteRep_coind W _
  have hunit : coindUnit (W : Subgroup G) M ≫ coindTrace (W : Subgroup G) M = 𝟙 M := by
    rw [coindUnit_comp_coindTrace]
    obtain ⟨c, hc⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    ext a
    change (W : Subgroup G).index • a = a
    rw [hc, add_smul, mul_comm, mul_smul, h2, smul_zero, zero_add, one_smul]
  refine eq_zero_tateCompactCohomologyRes_of_retract φ ψ _ _ hunit n ?_ x
  refine eq_zero_tateCompactCohomologyRes_coind_of_two_nsmul φ ψ n W (hW W) _
    (Rep.res (W : Subgroup G).subtype M) le_rfl (fun m => h2 m) ?_
  intro w
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' K₀ (w : G), w.2⟩
  refine ⟨k, ?_⟩
  have hk' : (w : G) ^ 2 ^ k ∈ K₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact congrArg Subtype.val hk
  have h1 := congrArg Units.val ((MonoidHom.mem_ker).1 hk')
  rw [Representation.asGroupHom_apply] at h1
  exact h1

end Tate

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

section Local

set_option maxHeartbeats 2000000 in

theorem subsingleton_cohomology_gsFinFamily_of_three_le {n : ℕ} (hn : n ≠ 0)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) (v : S) {j : ℕ} (hj : 3 ≤ j) :
    Subsingleton (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) j) := by
  refine subsingleton_cohomology_of_cdp_le_two hn (fun ℓ hℓ _ => ?_)
    (Rep.res (gsFinFamily S ιs v).toMonoidHom M) (fun m => hM m) hj
  refine cdp_galois_le_two _ _ hℓ ?_
  exact_mod_cast hℓ.ne_zero

set_option maxHeartbeats 2000000 in

theorem subsingleton_cohomology_real_of_odd (v : {v : InfinitePlace K.1 // v.IsReal}) {n : ℕ}
    (hn : Odd n) (A : Rep.{0} (ULift.{0} ℤ) Gal(AlgebraicClosure v.1.Completion / v.1.Completion))
    [IsDiscreteRep A] (hA : ∀ a : A, n • a = 0) {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (cohomology A j) := by
  suffices h : ∀ z : cohomology A j, z = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro z
  obtain ⟨U, hU⟩ := exists_card_smul_eq_zero A (by omega) z
  have hdvd : Nat.card (Gal(AlgebraicClosure v.1.Completion / v.1.Completion) ⧸ (U : Subgroup _)) ∣ 2 := by
    rw [← card_realGal_eq_two v.1 v.2, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_quotient_dvd_card _
  have h2 : 2 • z = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, mul_comm, mul_smul, hU, smul_zero]
  have hnz : n • z = 0 := nsmul_cohomology_eq_zero A hA j z
  obtain ⟨c, rfl⟩ := hn
  rw [add_smul, mul_comm, mul_smul, h2, smul_zero, zero_add, one_smul] at hnz
  exact hnz

end Local

section Criterion

theorem eq_zero_gsTateCompactCohomology_of_gsRealRes {n : ℕ} (hn : n ≠ 0)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 2 ≤ r)
    (hs : Function.Surjective (gsRealRes S ιr M (r + 1)).hom)
    (hi : Function.Injective (gsRealRes S ιr M (r + 2)).hom)
    (x : gsTateCompactCohomology S ιr ιs M (r + 2)) : x = 0 :=
  tateCompactCohomology_eq_zero_of_surjective_of_injective (gsFinFamily S ιs) (gsRealFamily S ιr) M _
    (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r
    ((surjective_tateGlobalToLocal_iff _ _ _ _ _ _ _ _ fun v =>
      subsingleton_cohomology_gsFinFamily_of_three_le S ιs hn M hM v (by omega)).2 hs)
    ((injective_tateGlobalToLocal_iff _ _ _ _ _ _ _ _ fun v =>
      subsingleton_cohomology_gsFinFamily_of_three_le S ιs hn M hM v (by omega)).2 hi) x

theorem eq_zero_gsTateCompactCohomology_of_subsingleton
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Subsingleton M]
    {r : ℕ} (hr : 4 ≤ r) (x : gsTateCompactCohomology S ιr ιs M r) : x = 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 2 := ⟨r - 2, by omega⟩
  refine eq_zero_gsTateCompactCohomology_of_gsRealRes S ιs ιr one_ne_zero M
    (fun m => Subsingleton.elim _ _) (by omega) (fun z => ⟨0, funext fun v => ?_⟩) ?_ x
  · have := subsingleton_cohomology_of_subsingleton (Rep.res (gsRealFamily S ιr v).toMonoidHom M) (p + 1)
    exact Subsingleton.elim _ _
  · have := subsingleton_cohomology_of_subsingleton M (p + 2)
    exact fun a b _ => Subsingleton.elim a b

end Criterion

section Odd

theorem eq_zero_gsTateCompactCohomology_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hM : ∀ m : M, ℓ • m = 0) {r : ℕ} (hr : 4 ≤ r) (x : gsTateCompactCohomology S ιr ιs M r) :
    x = 0 := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two h2
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 2 := ⟨r - 2, by omega⟩
  refine eq_zero_gsTateCompactCohomology_of_gsRealRes S ιs ιr hℓ.ne_zero M hM (by omega)
    (fun z => ⟨0, funext fun v => ?_⟩) ?_ x
  · have := subsingleton_cohomology_real_of_odd v hodd (Rep.res (gsRealFamily S ιr v).toMonoidHom M)
      (fun m => hM m) (j := p + 1) (by omega)
    exact Subsingleton.elim _ _
  · have : Subsingleton (cohomology M (p + 2)) :=
      subsingleton_cohomology_of_cdp_le_two hℓ.ne_zero
        (fun q hq hqℓ => cdp_galUnramifiedOutside_le_two_of_dvd K S hℓ.ne_zero hS (Or.inl hodd) hq hqℓ)
        M hM (by omega)
    exact fun a b _ => Subsingleton.elim a b

end Odd

section Devissage

theorem mem_of_natCast_mem_of_dvd {n d : ℕ} (hd : d ∣ n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : ((d : ℕ) : 𝓞 K.1) ∈ v.asIdeal) : v ∈ S := by
  refine hS v ?_
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

theorem eq_zero_gsTateCompactCohomology_of_coind
    (hC : (∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) →
      ∀ (W : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) {r : ℕ}, 4 ≤ r →
        ∀ x : gsTateCompactCohomology S ιr ιs (Rep.coind (W : Subgroup _).subtype
          (zmodRep.{0} (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) 2)) r, x = 0)
    {r : ℕ} (hr : 4 ≤ r) :
    ∀ (n : ℕ), n ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) →
      ∀ (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M],
        (∀ m : M, n • m = 0) → ∀ x : gsTateCompactCohomology S ιr ιs M r, x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hS M _ _ hM x
  by_cases hsub : Subsingleton M
  · exact eq_zero_gsTateCompactCohomology_of_subsingleton S ιs ιr M hr x
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hsub ⟨fun a b => by rw [← one_nsmul a, ← one_nsmul b, hM a, hM b]⟩
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨c, hc⟩ := hℓn
  let T : Submodule (ULift.{0} ℤ) M := LinearMap.ker (ℓ • LinearMap.id)
  have hmemT : ∀ m : M, m ∈ T ↔ ℓ • m = 0 := fun m => Iff.rfl
  have hT : ∀ g, T ≤ T.comap (M.ρ g) := fun g m hm => by
    change ℓ • M.ρ g m = 0
    rw [← map_nsmul, (hmemT m).1 hm, map_zero]
  have hSE := subQuotShortComplex_shortExact M T hT
  have : Finite (subQuotShortComplex M T hT).X₁ := Subtype.finite
  have : Finite (subQuotShortComplex M T hT).X₃ := Finite.of_surjective _ (Submodule.mkQ_surjective T)
  refine eq_zero_tateCompactCohomologyRes_of_shortExact (gsFinFamily S ιs) (gsRealFamily S ιr) hSE r
    ?_ ?_ x
  ·
    have hM₁ : ∀ m : M.subrepresentation T hT, ℓ • m = 0 := fun m => Subtype.ext ((hmemT m.1).1 m.2)
    by_cases h2 : ℓ = 2
    · subst h2
      exact eq_zero_tateCompactCohomologyRes_of_two_nsmul (gsFinFamily S ιs) (gsRealFamily S ιr) r
        (fun W => hC (mem_of_natCast_mem_of_dvd S ⟨c, hc⟩ hS) W hr) _ hM₁
    · exact eq_zero_gsTateCompactCohomology_of_odd S ιs ιr hℓ h2
        (mem_of_natCast_mem_of_dvd S ⟨c, hc⟩ hS) _ hM₁ hr
  ·
    have hc0 : c ≠ 0 := by rintro rfl; exact hn (by rw [hc, mul_zero])
    have hclt : c < n := by
      rw [hc]
      exact lt_mul_left (Nat.pos_of_ne_zero hc0) hℓ.one_lt
    refine ih c hclt hc0 (mem_of_natCast_mem_of_dvd S ⟨ℓ, by rw [hc, mul_comm]⟩ hS) _ ?_
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
    refine (map_nsmul T.mkQ c a).symm.trans ((Submodule.Quotient.mk_eq_zero T).2 ?_)
    rw [hmemT, ← mul_smul, ← hc]
    exact hM a

end Devissage

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem gsTateCompactCohomology_eq_zero {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 4 ≤ r) (x : gsTateCompactCohomology S ιr ιs M r) :
    x = 0 :=
  eq_zero_gsTateCompactCohomology_of_coind S ιs ιr
    (fun h2S W _ hr' y => gsTateCompactCohomology_coind_zmodRep_two_eq_zero S ιr h2S ιs W hr' y)
    hr n hn hS M hM x

theorem subsingleton_gsTateCompactCohomology {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
    Subsingleton (gsTateCompactCohomology S ιr ιs M r) :=
  ⟨fun x y => (gsTateCompactCohomology_eq_zero S ιr ιs hn hS M hM hr x).trans
    (gsTateCompactCohomology_eq_zero S ιr ιs hn hS M hM hr y).symm⟩

set_option maxHeartbeats 4000000 in

theorem injective_gsRealRes_of_four_le {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
    Function.Injective (gsRealRes S ιr M r).hom := by
  obtain ⟨ιs'⟩ : Nonempty (∀ v : S,
      ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
    ⟨fun _ => Classical.choice nonempty_algHom_of_isSepClosed⟩
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  exact (injective_tateGlobalToLocal_iff (gsFinFamily S ιs') (gsRealFamily S ιr) M
    (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) (p + 1)
    (fun v => subsingleton_cohomology_gsFinFamily_of_three_le S ιs' hn M hM v (by omega))).1
    (injective_tateGlobalToLocal_of_eq_zero (gsFinFamily S ιs') (gsRealFamily S ιr) M
      (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) p
      (gsTateCompactCohomology_eq_zero S ιr ιs' hn hS M hM hr))

set_option maxHeartbeats 4000000 in

theorem surjective_gsRealRes_of_three_le {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) :
    Function.Surjective (gsRealRes S ιr M r).hom := by
  obtain ⟨ιs'⟩ : Nonempty (∀ v : S,
      ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
    ⟨fun _ => Classical.choice nonempty_algHom_of_isSepClosed⟩
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  exact (surjective_tateGlobalToLocal_iff (gsFinFamily S ιs') (gsRealFamily S ιr) M
    (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
    (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) (p + 1)
    (fun v => subsingleton_cohomology_gsFinFamily_of_three_le S ιs' hn M hM v (by omega))).1
    (surjective_tateGlobalToLocal_of_eq_zero (gsFinFamily S ιs') (gsRealFamily S ιr) M
      (fun v => Rep.res (gsFinFamily S ιs' v).toMonoidHom M) (fun _ => 𝟙 _)
      (fun w => Rep.res (gsRealFamily S ιr w).toMonoidHom M) (fun _ => 𝟙 _) p
      (gsTateCompactCohomology_eq_zero S ιr ιs' hn hS M hM (by omega)))

end

end GroundTheory.ProfCoh
end
