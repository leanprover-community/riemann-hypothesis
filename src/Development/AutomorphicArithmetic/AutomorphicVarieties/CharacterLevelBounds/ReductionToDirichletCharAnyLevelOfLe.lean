import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LayerLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0LocalCardBoundedOfClsKerLeKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PartModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SignLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.VLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CokerAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LiftGens
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactLeLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SumBack
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaAbsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactorGS
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ExistsNumberFieldIsAbFieldFinrankEqDeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.layerex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem kerFin_triv {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)
    (U' U : Subgroup G) (h : U' ≤ U) (hρ : ∀ u ∈ U, ∀ m, ρ u m = m) (n : ℕ) (hn : ∀ u ∈ U, u ^ n ∈ U')
    [Fintype (U ⧸ U'.subgroupOf U)] :
    Module.length R (LinearMap.ker (resU ρ h)) ≤ (Fintype.card (U ⧸ U'.subgroupOf U) : ℕ∞) *
      Module.length R (LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M))) := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  set N := LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M)) with hN
  have hadd : ∀ z ∈ Z1U ρ U, ∀ a b : U, z (a * b) = z a + z b := by
    intro z hz a b
    have := ((mem_Z1_iff_cocycle (ρ.comp U.subtype) z).mp hz).2 a b
    rw [this, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ a a.2]
  have hone : ∀ z ∈ Z1U ρ U, z 1 = 0 := by
    intro z hz
    have := hadd z hz 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ z ∈ Z1U ρ U, ∀ a : U, z a⁻¹ = - z a := by
    intro z hz a
    have := hadd z hz a a⁻¹
    rw [mul_inv_cancel, hone z hz] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hpow : ∀ z ∈ Z1U ρ U, ∀ a : U, ∀ k : ℕ, z (a ^ k) = k • z a := by
    intro z hz a k
    induction k with
    | zero => rw [pow_zero, hone z hz, zero_smul]
    | succ k ih => rw [pow_succ, hadd z hz, ih, succ_nsmul]
  have hB : ∀ z ∈ Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype)), (z : U → M) = 0 := by
    intro z hz
    rw [Submodule.mem_comap, B1, LinearMap.mem_range] at hz
    obtain ⟨m, hm⟩ := hz
    funext u
    rw [Submodule.coe_subtype] at hm
    rw [← hm, amitsur_d0_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ u u.2, sub_self]
    rfl
  let ev : (Z1U ρ U) →ₗ[R] (U ⧸ K → M) :=
    LinearMap.pi (fun q => (LinearMap.proj (Quotient.out q) : (U → M) →ₗ[R] M) ∘ₗ (Z1U ρ U).subtype)
  have hev : ∀ z q, ev z q = (z : U → M) (Quotient.out q) := fun z q => rfl
  let Φ : H1U ρ U →ₗ[R] (U ⧸ K → M) :=
    (Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype))).liftQ ev (by
      intro z hz
      rw [LinearMap.mem_ker]
      funext q
      rw [hev, hB z hz]
      rfl)
  have hΦ : ∀ z q, Φ (Submodule.Quotient.mk z) q = (z : U → M) (Quotient.out q) := fun z q => rfl
  have hvan : ∀ z : Z1U ρ U, resU ρ h (Submodule.Quotient.mk z) = 0 → ∀ u : U, (u : G) ∈ U' → (z : U → M) u = 0 := by
    intro z hz u hu
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).mp hz
    have := hm ⟨(u : G), hu⟩
    rw [hρ _ (h hu), sub_self] at this
    exact this
  have key : ∀ x ∈ LinearMap.ker (resU ρ h), ∀ q, Φ x q ∈ N := by
    intro x hx q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    rw [hΦ, hN, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul,
      ← hpow z z.2]
    exact hvan z hx _ (hn _ (Quotient.out q).2)
  let Ψ : LinearMap.ker (resU ρ h) →ₗ[R] (U ⧸ K → N) :=
    LinearMap.pi (fun q => LinearMap.codRestrict N
      ((LinearMap.proj q : (U ⧸ K → M) →ₗ[R] M) ∘ₗ Φ ∘ₗ (LinearMap.ker (resU ρ h)).subtype)
      (fun x => key x.1 x.2 q))
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hxk⟩ hx0
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hq : ∀ q : U ⧸ K, (z : U → M) (Quotient.out q) = 0 := by
      intro q
      have := congrArg (fun f => ((f q : N) : M)) hx0
      exact this
    have hz : (z : U → M) = 0 := by
      funext u
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K u
      have hkU : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
      have hu : u = Quotient.out (QuotientGroup.mk u : U ⧸ K) * (k : U)⁻¹ := by
        rw [hk]; group
      rw [hu, hadd z z.2, hq, hinv z z.2, hvan z hxk _ hkU, neg_zero, add_zero]
      rfl
    have hz' : z = 0 := Subtype.ext hz
    subst hz'
    rfl
  calc Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (U ⧸ K → N) :=
        Module.length_le_of_injective Ψ hΨ
    _ = _ := by
      rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

private theorem exists_doubleCoset_section {G : Type} [Group G] (U' U : Subgroup G) (h0 : U'.relIndex U ≠ 0) :
    ∃ T : Finset G, (T : Set G) ⊆ U ∧ T.card ≤ U'.relIndex U ∧ U ≤ Subgroup.closure (T : Set G) ⊔ U' := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (Quotient.out q).2
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]
  · intro u hu
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)
    have hkU' : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
    have hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure
        ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp
    have heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹ := by
      have := congrArg (fun x : U => (x : G)) hk
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hout (U'.inv_mem hkU')

theorem UpperTheory.V.Chr.kerFin :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* Oˣ), ContAction (twist₂ l θ) →
          ∀ (U' U : Subgroup G) (h : U' ≤ U), U' ≤ θ.ker → (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ n : ℕ, n ≠ 0 → U'.relIndex U ∣ n →
          Module.length O (LinearMap.ker (resU (twist₂ l θ) h)) ≤ ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
  intro l _ O _ _ _ _ _ G _ _ _ θ hc U' U h hker hcomm n hn hdiv
  classical
  have h0 : U'.relIndex U ≠ 0 := fun hz => hn (Nat.eq_zero_of_zero_dvd (hz ▸ hdiv))
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  have hnorm : K.Normal := by
    constructor
    intro k hk g
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    have hcm := hcomm g g.2 k k.2
    have : ((g * k * g⁻¹ : U) : G) = ((g : G) * k * (g : G)⁻¹ * (k : G)⁻¹) * k := by
      push_cast; group
    rw [this]
    exact U'.mul_mem hcm hk
  have hcardK : Nat.card (U ⧸ K) = U'.relIndex U := by
    rw [Subgroup.relIndex, ← hK, Subgroup.index]
  have hpowU : ∀ u ∈ U, u ^ n ∈ U' := by
    intro u hu
    obtain ⟨c, hc'⟩ := hdiv
    have h1 : (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) ^ (U'.relIndex U) = 1 := by
      rw [← hcardK]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf] at h1
    rw [hc', pow_mul]
    have : ((⟨u, hu⟩ : U) ^ (U'.relIndex U) : U) = (u ^ (U'.relIndex U) : G) := by simp
    rw [this] at h1
    exact U'.pow_mem h1 c
  have hrel_le : U'.relIndex U ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
  obtain ⟨_, hζ, heOtop, _⟩ := rootVal l O n hn
  have hact : ∀ g m, twist₂ l θ g m = ((θ g : Oˣ) : O) • m := fun g m => by
    rw [twist₂, scalRep_apply]
  by_cases htriv : U ≤ θ.ker
  · have hρ : ∀ u ∈ U, ∀ m, twist₂ l θ u m = m := by
      intro u hu m
      rw [hact, htriv hu, Units.val_one, one_smul]
    have := kerFin_triv (twist₂ l θ) U' U h hρ n hpowU
    refine this.trans ?_
    rw [(qoFacts l O).2.2.2, (rootVal l O n hn).1, Fintype.card_eq_nat_card, hcardK]
    push_cast
    rw [← mul_assoc]
    gcongr
  · obtain ⟨g, hg, hgk⟩ := SetLike.not_le_iff_exists.mp htriv
    set ζ : O := ((θ g : Oˣ) : O) with hζdef
    have hθn : (θ g) ^ n = 1 := by
      rw [← map_pow]
      exact hker (hpowU g hg)
    have hζn : ζ ^ n = 1 := by
      rw [hζdef, ← Units.val_pow_eq_pow_val, hθn, Units.val_one]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hgk
      rw [MonoidHom.mem_ker]
      exact Units.ext h1
    have hsub : H0U (twist₂ l θ) U ≤ ((ζ - 1) • LinearMap.id : QO l O →ₗ[O] QO l O).ker := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm
      have h1 := hm ⟨g, hg⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact] at h1
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul, hζdef, h1, sub_self]
    have hbound : Module.length O (H0U (twist₂ l θ) U) ≤ (n.factorization l : ℕ∞) * eO l O := by
      refine (Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)).trans ?_
      rw [(qoFacts l O).2.2.2]
      exact hζ ζ hζn hζ1
    obtain ⟨T, hTU, hTcard, hTcl⟩ := exists_doubleCoset_section U' U h0
    have key := kerResAb O G (QO l O) (twist₂ l θ) hc (qoFacts l O).1
      (fun g => ⟨(θ g : O), fun m => hact g m⟩) U' U h hcomm T hTU
      (hTcl.trans (Subgroup.le_topologicalClosure _))
    refine key.trans ?_
    have hle : T.card ≤ n := hTcard.trans hrel_le
    calc (T.card : ℕ∞) * Module.length O (H0U (twist₂ l θ) U) ≤ (n : ℕ∞) * ((n.factorization l : ℕ∞) * eO l O) := by
          gcongr
      _ = ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
          push_cast
          rw [mul_assoc]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem exists_reps {G : Type} [Group G] (U' U : Subgroup G) (h0 : U'.relIndex U ≠ 0) :
    ∃ T : Finset G, (T : Set G) ⊆ U ∧ T.card ≤ U'.relIndex U ∧ U ≤ Subgroup.closure (T : Set G) ⊔ U' := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (Quotient.out q).2
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]
  · intro u hu
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)
    have hkU' : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
    have hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure
        ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp
    have heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹ := by
      have := congrArg (fun x : U => (x : G)) hk
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hout (U'.inv_mem hkU')

theorem UpperTheory.V.Chr.kerIdx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* Oˣ), ContAction (twist₂ l θ) →
          ∀ (U' U : Subgroup G) (h : U' ≤ U), (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ n : ℕ, n ≠ 0 → U'.relIndex U ∣ n →
          Module.length O (LinearMap.ker (resU (twist₂ l θ) h)) ≤ (n : ℕ∞) * Module.length O (H0U (twist₂ l θ) U) := by
  intro l _ O _ _ _ _ _ G _ _ _ θ hθ U' U h hab n hn hd
  obtain ⟨T, hT, hc, hU⟩ := exists_reps U' U (ne_zero_of_dvd_ne_zero hn hd)
  have key := UpperTheory.V.Base.kerResAb O G (QO l O) (twist₂ l θ) hθ (UpperTheory.V.Base.qoFacts l O).1
    (fun g => ⟨((θ g : Oˣ) : O), fun _ => rfl⟩) U' U h hab T hT (hU.trans (Subgroup.le_topologicalClosure _))
  refine key.trans ?_
  have : (T.card : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hc.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
  gcongr
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]
  exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

private theorem comm_inf {G : Type} [Group G] (U' D : Subgroup G) (h : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ U') :
    ∀ a ∈ ⊤ ⊓ D, ∀ b ∈ ⊤ ⊓ D, a * b * a⁻¹ * b⁻¹ ∈ U' ⊓ D := fun a ha b hb =>
  ⟨h a b, D.mul_mem (D.mul_mem (D.mul_mem ha.2 hb.2) (D.inv_mem ha.2)) (D.inv_mem hb.2)⟩

theorem UpperTheory.V.Chr.eigLe :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → levH ℚ Ω H ≤ ψ.ker →
          eigL l e (levH ℚ Ω H) ψ ≤ V l e ψ + (loss l N H.index e : ℕ∞) * eO l O := by
  intro Ω _ _ _ N _ H l hl O _ _ _ _ _ e ψ he hψ
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨hopen, -, -, -, hine⟩ := clsFacts ℚ Ω N
  obtain ⟨hex, hN, hconj⟩ := placesQ Ω
  have hk : (cls ℚ Ω N).ker ≤ levH ℚ Ω H := fun g hg => by
    show cls ℚ Ω N g ∈ H
    rw [MonoidHom.mem_ker.1 hg]
    exact H.one_mem
  have hUo : IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := Subgroup.isOpen_mono hk hopen
  have hψi : levH ℚ Ω H ≤ (ψ⁻¹).ker := fun g hg => by
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, MonoidHom.mem_ker.1 (hψ hg), inv_one]
  have hc : ContAction (rho l e ψ) := (contTw ℚ Ω l).2.2 O ψ⁻¹ _ (Subgroup.isOpen_mono hψi hUo)
  have hcomm : ∀ a b : G ℚ Ω, a * b * a⁻¹ * b⁻¹ ∈ levH ℚ Ω H := fun a b => by
    show cls ℚ Ω N _ ∈ H
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, mul_inv_cancel]
    exact H.one_mem
  have hn : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hdvd : (levH ℚ Ω H).relIndex ⊤ ∣ H.index := by
    rw [Subgroup.relIndex_top_right, levH, Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  obtain ⟨hb1, hb2⟩ := H0_local_card_bounded_of_cls_ker_le_ker Ω l O N e ψ he (hk.trans hψ)
  obtain ⟨A₀, hA₀⟩ := hex l hl.out
  have hA : ∀ p : N.primeFactors, ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧
      ∀ A' : ValuationSubring Ω, A'.valuation ((p : ℕ) : Ω) < 1 → ¬ A'.valuation (l : Ω) < 1 →
        ∃ u : G ℚ Ω, ∀ x ∈ Ine (F := ℚ) A', u⁻¹ * x * u ∈ Ine (F := ℚ) A := by
    intro p
    by_cases h : ∃ A : ValuationSubring Ω, A.valuation ((p : ℕ) : Ω) < 1 ∧ ¬ A.valuation (l : Ω) < 1
    · obtain ⟨A, h1, h2⟩ := h
      exact ⟨A, h2, fun A' h3 _ =>
        (hconj p A' A (Nat.prime_of_mem_primeFactors p.2) h3 h1).imp fun _ hu => hu.2⟩
    · exact ⟨⊤, ((places ℚ Ω l ⊤).2.1 rfl).2, fun A' h3 h4 => absurd ⟨A', h3, h4⟩ h⟩
  choose A hAl hAc using hA
  have hID : ∀ B : ValuationSubring Ω, Ine (F := ℚ) B ≤ Dec (F := ℚ) B := fun _ _ h => h.1
  let D : Option N.primeFactors → Subgroup (G ℚ Ω) := fun i => i.elim (Dec (F := ℚ) A₀) fun p => Ine (F := ℚ) (A p)
  have h1 := selDown O _ _ (rho l e ψ) (levH ℚ Ω H) ⊤ le_top _ (conjStable_shaFam ℚ Ω l) _ D
    (by
      rintro (_ | p)
      · exact Or.inl ⟨A₀, hA₀, rfl⟩
      · exact Or.inr ⟨A p, rfl⟩)
    (by
      have hd : ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
          ∃ u : G ℚ Ω, ∀ x ∈ Dec (F := ℚ) B, u⁻¹ * x * u ∈ D none := fun B hB =>
        (hconj l B A₀ hl.out hB hA₀).imp fun _ hu => hu.1
      rintro _ (⟨B, hB, rfl⟩ | ⟨B, rfl⟩)
      · obtain ⟨u, hu⟩ := hd B hB
        exact Or.inr ⟨none, u, trivial, fun x hx => hu x hx.2⟩
      · by_cases hB : B.valuation (l : Ω) < 1
        · obtain ⟨u, hu⟩ := hd B hB
          exact Or.inr ⟨none, u, trivial, fun x hx => hu x (hID B hx.2)⟩
        · by_cases hB' : B.valuation (N : Ω) < 1
          · obtain ⟨p, hp, hp'⟩ := (hN B N (NeZero.ne N)).1 hB'
            obtain ⟨u, hu⟩ := hAc ⟨p, hp⟩ B hp' hB
            exact Or.inr ⟨some ⟨p, hp⟩, u, trivial, fun x hx => hu x hx.2⟩
          · exact Or.inl (inf_le_right.trans ((hine B hB').trans hk)))
  have h2 := (selTwist O _ _ (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) (rho l e ψ) ψ (tw_apply l e ψ) (levH ℚ Ω H)
    (fun u hu => hψ hu) _ (conjStable_shaFam ℚ Ω l)).2 ⊤ 1
  rw [mul_one] at h2
  have h3 := cokerAb O _ _ (rho l e ψ) hc (qoFacts l O).1 (fun g => ⟨_, fun _ => rfl⟩) (levH ℚ Ω H) ⊤ le_top
    isClosed_univ (hUo.preimage continuous_subtype_val) fun a _ b _ => hcomm a b
  have h3' := h3.trans (mul_le_mul' (pow_le_pow_left' (Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)) 2) hb2)
  have h4 := (kerIdx l O _ _ hc _ _ (inf_le_inf_right (D none) (le_top : levH ℚ Ω H ≤ ⊤)) (comm_inf _ _ hcomm) _ hn
    ((relIndex_inf_dvd _ _ _).trans hdvd)).trans (mul_le_mul' le_rfl (hb1 A₀ _ hA₀ (le_inf le_top (hID A₀))))
  have h5 : ∀ p : N.primeFactors, _ := fun p =>
    kerFin l O _ _ hc _ _ (inf_le_inf_right (D (some p)) (le_top : levH ℚ Ω H ≤ ⊤)) (fun g hg => by
      have e1 : chiO ℚ Ω l O g = 1 := by
        have := MonoidHom.mem_ker.1 ((places ℚ Ω l (A p)).2.2.2 (hAl p) hg.2)
        rw [chiO, MonoidHom.comp_apply, this, map_one]
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 (hψi hg.1), one_mul]
      show chiO ℚ Ω l O g ^ (-(e : ℤ)) = 1
      rw [e1, one_zpow]) (comm_inf _ _ hcomm) _ hn ((relIndex_inf_dvd _ _ _).trans hdvd)
  rw [Fintype.sum_option] at h1
  have h6 := (Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => h5 p).trans_eq (Finset.sum_const _)
  refine (h2.le.trans (h1.trans (add_le_add (add_le_add le_rfl (add_le_add h4 h6)) h3'))).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, loss, add_assoc]
  congr 1
  push_cast
  ring
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

namespace UpperTheory.V.Chr

section Red

variable (E : Type) [Field E] [NumberField E] [IsCMField E] {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ}
  {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {Ω' : Type} [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
  (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem levH_le_ker {s : ℕ} {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) : levH ℚ Ω H ≤ (dirG ℚ Ω χ).ker :=
  fun _ hg => h.1 hg

theorem levH_facts : (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) :=
  ⟨Subgroup.index_comap_of_surjective _ (clsOnto Ω N).1,
    Subgroup.isOpen_mono (H₁ := (cls ℚ Ω N).ker) (fun g hg => by
      show cls ℚ Ω N g ∈ H
      rw [MonoidHom.mem_ker.1 hg]; exact one_mem _) (clsFacts ℚ Ω N).1⟩

theorem reduction_to_dirichletChar_any_level (hE : HasLevel E N H) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))] (h2 : l ≠ 2)
    {e : ℕ} (he : e ≠ 0) (T : Finset (DirichletCharacter O N)) :
    (↑T = evenSet O H e → plusLen D e * eO l O ≤
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O)) ∧
    (↑T = evenSet O H (e + 1) → minusLen D e * eO l O ≤
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O)) := by
  obtain ⟨c, hc, hp, hm⟩ := partModel E N H hE l O Ω' D Ω e
  rw [(levGal E N H hE).2.1, hp, hm]
  exact ⟨fun hT => (signLe Ω N H l O h2 e _ c hc T hT.ge).trans (Finset.sum_le_sum fun χ hχ =>
      eigLe Ω N H l O e _ he (levH_le_ker O Ω (hT.le hχ))),
    fun hT => (signLe Ω N H l O h2 e _ c hc T hT.ge).trans (Finset.sum_le_sum fun χ hχ =>
      eigLe Ω N H l O e _ he (levH_le_ker O Ω (hT.le hχ)))⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem dirG_pow {s : ℕ} {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) : dirG ℚ Ω χ ^ H.index = 1 := by
  unfold evenSet at h
  have hH : H ≤ (MulChar.toUnitHom χ).ker := h.1
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  unfold dirG
  rw [MonoidHom.comp_apply, ← map_pow, ← MonoidHom.mem_ker]
  exact hH (H.pow_index_mem _)

theorem V_le_V' {s e : ℕ} (he : e ≠ 0) {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) {N' : ℕ} (hN : N' ≠ 0) :
    V l e (dirG ℚ Ω χ) ≤ V' l N' e (dirG ℚ Ω χ) + ((N'.primeFactors.card * H.index.factorization l : ℕ) : ℕ∞) * eO l O ∧
    (¬ l ∣ H.index → V l e (dirG ℚ Ω χ) = V' l N' e (dirG ℚ Ω χ)) := by
  have hopen : IsOpen ((dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono (levH_le_ker (O := O) (Ω := Ω) h) (levH_facts (Ω := Ω) (H := H)).2
  have hpow := dirG_pow (O := O) (Ω := Ω) h
  exact vLe Ω l O N' e H.index _ hN he Subgroup.index_ne_zero_of_finite hopen hpow

theorem reduction_to_dirichletChar_any_level_of_le (hE : HasLevel E N H) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))] (h2 : l ≠ 2)
    {e : ℕ} (he : e ≠ 0) (T : Finset (DirichletCharacter O N)) {N' : ℕ} (hN : N' ≠ 0) :
    (↑T = evenSet O H e → plusLen D e * eO l O ≤ ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
      ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O)) ∧
    (↑T = evenSet O H (e + 1) → minusLen D e * eO l O ≤ ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
      ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O)) := by
  have hrank : Module.finrank ℚ E = H.index := (levGal E N H hE).2.1
  have key := reduction_to_dirichletChar_any_level (E := E) (O := O) (D := D) (Ω := Ω) hE h2 he T
  have hsum : ∀ s, (↑T : Set (DirichletCharacter O N)) = evenSet O H s →
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O) ≤
        ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
          ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O) := by
    intro s hT
    refine Finset.sum_le_sum fun χ hχ => ?_
    have hχ' : χ ∈ evenSet O H s := by rw [← hT]; exact hχ
    have h1 := (V_le_V' (l := l) (O := O) (Ω := Ω) he hχ' hN).1
    rw [hrank]
    calc V l e (dirG ℚ Ω χ) + (loss l N H.index e : ℕ∞) * eO l O
        ≤ (V' l N' e (dirG ℚ Ω χ) + ((N'.primeFactors.card * H.index.factorization l : ℕ) : ℕ∞) * eO l O) +
          (loss l N H.index e : ℕ∞) * eO l O := add_le_add h1 le_rfl
      _ = _ := by push_cast; ring
  exact ⟨fun hT => (key.1 hT).trans (hsum e hT), fun hT => (key.2 hT).trans (hsum (e + 1) hT)⟩

end Red

end UpperTheory.V.Chr

end
end
