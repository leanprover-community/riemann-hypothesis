import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfMemInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem

section
open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.alg :
    UpperTheory.V.Z.Kato.Sym.PE.Alg := by
  intro Ω _ _ _ ε X
  have hinj : Function.Injective (pj X) :=
    (io X).injective.comp (transcendental_iff_injective.1 (jK_transcendental X))
  let φ : RatFunc Ω →+* Kb X := IsFractionRing.lift hinj
  have hφ : ∀ p : Polynomial Ω, φ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = pj X p := fun p => IsFractionRing.lift_algebraMap hinj p
  refine ⟨φ, hφ, ?_⟩
  have hinj0 : Function.Injective (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := transcendental_iff_injective.1 (jK_transcendental X)
  let ψ : RatFunc Ω →+* X.K := IsFractionRing.lift hinj0
  have hψ : ∀ p : Polynomial Ω, ψ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = aeval X.jK p := fun p => IsFractionRing.lift_algebraMap hinj0 p
  letI : Algebra (RatFunc Ω) X.K := ψ.toAlgebra
  have hc : φ = algebraMap (RatFunc Ω) (Kb X) := RingHom.ext fun z => by
    change φ z = io X (ψ z)
    rw [← RatFunc.num_div_denom z, map_div₀, map_div₀, map_div₀, hφ, hφ, hψ, hψ]
    rfl
  have hle : ∀ y ∈ IntermediateField.adjoin Ω {X.jK}, y ∈ ψ.fieldRange := fun y hy => by
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff Ω y).1 hy
    exact ⟨algebraMap _ _ r / algebraMap _ _ s, by rw [map_div₀, hψ, hψ]⟩
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun f => by
    obtain ⟨p, hp, he⟩ := X.alg_j f
    have hl : p.map (algebraMap _ X.K) ∈ lifts ψ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact hle _ (p.coeff n).2
    obtain ⟨q, hq⟩ := (mem_lifts _).1 hl
    refine ⟨q, ?_, ?_⟩
    · rintro rfl
      rw [Polynomial.map_zero] at hq
      exact hp ((Polynomial.map_eq_zero _).1 hq.symm)
    · change eval₂ ψ f q = 0
      rw [← eval_map, hq, eval_map]
      exact he⟩
  have hA := Algebra.IsAlgebraic.trans (RatFunc Ω) X.K (Kb X)
  refine @Algebra.IsAlgebraic.mk _ _ _ _ φ.toAlgebra fun z => ?_
  obtain ⟨p, hp, he⟩ := hA.isAlgebraic z
  refine ⟨p, hp, ?_⟩
  change eval₂ φ z p = 0
  rw [hc]
  exact he
end

section
open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.integ :
    UpperTheory.V.Z.Kato.Sym.PE.Integ := by
  intro Ω _ _ _ ε X m hm u z hu hz
  have key : ∀ w : X.K, IsU X w → (pj X).IsIntegralElem (io X w) := by
    intro w hw
    let φ : Polynomial Ω →+* X.K := (aeval X.jK).toRingHom
    have hmem : w ∈ (integralClosure (Subring.closure (φ.range : Set X.K)) X.K).toSubring := by
      rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
      rintro ⟨V, hV⟩
      have hov : X.OverY V := ⟨fun c => hV ⟨C c, by simp [φ]⟩, hV ⟨Polynomial.X, by simp [φ]⟩⟩
      exact (V.valuation_le_one_iff w).1 (hw.2 V hov).le
    obtain ⟨p, hp, hpw⟩ := hmem
    have hle : Subring.closure (φ.range : Set X.K) ≤ φ.range := Subring.closure_le.2 subset_rfl
    have hlift : p.map (algebraMap (Subring.closure (φ.range : Set X.K)) X.K) ∈ lifts φ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact RingHom.mem_range.1 (hle (p.coeff n).2)
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift (hp.map _)
    refine ⟨Q, hQm, ?_⟩
    show eval₂ ((io X).comp φ) (io X w) Q = 0
    rw [← hom_eval₂, ← eval_map, hQ, eval_map, hpw, _root_.map_zero]
  have hu0 : io X u ≠ 0 := (_root_.map_ne_zero _).2 hu.1
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz
    exact hu0 hz.symm
  have hinv : IsU X u⁻¹ := ⟨inv_ne_zero hu.1, fun W hW => by rw [map_inv₀, hu.2 W hW, inv_one]⟩
  refine ⟨hz0, ?_, ?_⟩
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [hz]
    exact key u hu
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [inv_pow, hz, ← map_inv₀]
    exact key _ hinv
end

section
open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.lcFin :
    UpperTheory.V.Z.Kato.Sym.PE.LcFin := by
  classical
  intro F E A _ _ _ _ U hU η hη
  have hS : ∀ g : U, IsOpen {x : Gal(E/F) | x ∈ U ∧ η x = η g} := by
    intro g
    have := hU.isOpenMap_subtype_val _ (hη.isOpen_fiber (η g))
    convert this using 1
    ext x
    constructor
    · rintro ⟨hx, hxg⟩
      exact ⟨⟨x, hx⟩, hxg, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  have hN : ∀ g : U, ∃ L : IntermediateField F E, FiniteDimensional F L ∧
      (L.fixingSubgroup : Set Gal(E/F)) ⊆
        {y | (g : Gal(E/F)) * y ∈ U ∧ η ((g : Gal(E/F)) * y) = η g} := by
    intro g
    rw [← krullTopology_mem_nhds_one_iff]
    refine IsOpen.mem_nhds ((hS g).preimage (continuous_const.mul continuous_id)) ?_
    simp [g.2]
  choose L hLfd hLsub using hN
  have hfg : ∀ g : U, ∃ s : Finset E,
      Submodule.span F (s : Set E) = Subalgebra.toSubmodule (L g).toSubalgebra := by
    intro g
    haveI := hLfd g
    exact (Submodule.fg_iff_finiteDimensional _).2 (inferInstanceAs (FiniteDimensional F (L g)))
  choose s hs using hfg
  have hcpt : IsCompact (U : Set Gal(E/F)) := (Subgroup.isClosed_of_isOpen U hU).isCompact
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover
    (fun g : U => {x : Gal(E/F) | (g : Gal(E/F))⁻¹ * x ∈ (L g).fixingSubgroup})
    (fun g => by
      haveI := hLfd g
      exact (IntermediateField.fixingSubgroup_isOpen (L g)).preimage
        (continuous_const.mul continuous_id))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [one_mem]⟩)
  refine ⟨t.biUnion s, ?_⟩
  intro h hh h' hh' hag
  obtain ⟨g, hgt, hg⟩ := Set.mem_iUnion₂.1 (ht hh)
  have hg0 : (g : Gal(E/F))⁻¹ * h ∈ (L g).fixingSubgroup := hg
  have hsame : ∀ x ∈ L g, h x = h' x := by
    intro x hx
    have hx' : x ∈ Submodule.span F (s g : Set E) := by
      rw [hs g]
      exact hx
    exact LinearMap.eqOn_span' (f := h.toLinearMap) (g := h'.toLinearMap)
      (fun b hb => hag b (Finset.mem_biUnion.2 ⟨g, hgt, hb⟩)) hx'
  have hg' : (g : Gal(E/F))⁻¹ * h' ∈ (L g).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg0 ⊢
    intro x hx
    rw [AlgEquiv.mul_apply, ← hsame x hx, ← AlgEquiv.mul_apply]
    exact hg0 x hx
  have e1 := (hLsub g hg0).2
  have e2 := (hLsub g hg').2
  simp only [mul_inv_cancel_left] at e1 e2
  rw [e1, e2]
end

section
open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

namespace UpperTheory.V.Z.Kato.Sym.PE

private def FinalTheorems : Prop :=
  ∀ (k F Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field Ω] [Algebra F (RatFunc k)] [Algebra (RatFunc k) Ω] [Algebra F Ω] [IsScalarTower F (RatFunc k) Ω] [Algebra k[X] Ω] [IsScalarTower k[X] (RatFunc k) Ω] [IsAlgClosure (RatFunc k) Ω] [Algebra.IsAlgebraic F Ω] (N : ℕ) [NeZero N] (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (U : Subgroup (Ω ≃ₐ[F] Ω)), IsOpen (U : Set (Ω ≃ₐ[F] Ω)) → ∀ α β : Ω, α ≠ 0 → β ≠ 0 → IsIntegral k[X] α → IsIntegral k[X] α⁻¹ → IsIntegral k[X] β → IsIntegral k[X] β⁻¹ → (∀ g ∈ U, g (α ^ N) = α ^ N ∧ g (β ^ N) = β ^ N) → ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N, IsLocallyConstant (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) ∧ (∀ g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ h ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, GlobalTheory.NeedB.kum (N := N) ζ α g * GlobalTheory.NeedB.kum ζ β h = η₀ h - η₀ (g * h) + η₀ g) ∧ ∀ r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ B : ValuationSubring Ω, (∀ p : k[X], algebraMap k[X] Ω p ∈ B) → GlobalTheory.NeedB.Inert B r → η₀ r = 0 ∧ r α = α ∧ r β = β

private theorem existsUnique_eq_primitiveRoot_pow_mul_of_pow_eq {E : Type} [Field E] {m : ℕ} [NeZero m] {ζ a c : E}
    (hζ : IsPrimitiveRoot ζ m) (ha : a ≠ 0) (hc : c ^ m = a ^ m) :
    ∃! i : ZMod m, c = ζ ^ i.val * a := by
  have h1 : (c / a) ^ m = 1 := by rw [div_pow, hc, div_self (pow_ne_zero _ ha)]
  obtain ⟨k, hk, hk'⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hck : c = ζ ^ k * a := by rw [hk', div_mul_cancel₀ _ ha]
  refine ⟨(k : ZMod m), ?_, ?_⟩
  · show c = ζ ^ (k : ZMod m).val * a
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    exact hck
  · intro j hj
    have e : ζ ^ j.val = ζ ^ k := mul_right_cancel₀ ha (hj.symm.trans hck)
    have := hζ.pow_inj (ZMod.val_lt j) hk e
    rw [← ZMod.natCast_zmod_val j, this]

private theorem etaEx_of (hS : FinalTheorems) (hA : Alg) (hI : Integ) (hL : LcFin) : EtaEx := by
  intro Ω _ _ _ ε X m hm u v a b hu hv ha hb
  obtain ⟨φ, hφ, halg⟩ := hA Ω ε X
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  haveI : NeZero m := ⟨hm.ne'⟩
  letI alg1 : Algebra (RatFunc Ω) (Kb X) := φ.toAlgebra
  letI alg2 : Algebra (Polynomial Ω) (Kb X) := (pj X).toAlgebra
  haveI tw : IsScalarTower (Polynomial Ω) (RatFunc Ω) (Kb X) :=
    IsScalarTower.of_algebraMap_eq fun p => (hφ p).symm
  haveI : IsAlgClosed (Kb X) := by unfold Kb; infer_instance
  haveI : IsAlgClosure (RatFunc Ω) (Kb X) := ⟨inferInstance, halg⟩
  haveI : IsGalois (RatFunc Ω) (Kb X) := inferInstance
  let L := IntermediateField.adjoin (RatFunc Ω) ({io X u, io X v} : Set (Kb X))
  haveI : FiniteDimensional (RatFunc Ω) L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hU : IsOpen (L.fixingSubgroup : Set (Kb X ≃ₐ[RatFunc Ω] Kb X)) :=
    IntermediateField.fixingSubgroup_isOpen L
  have hζ : IsPrimitiveRoot (zt X m) m :=
    (isPrimitiveRoot_eOm ε hm.ne').map_of_injective
      (f := (algebraMap X.K (Kb X)).comp (algebraMap Ω X.K)) (RingHom.injective _)
  obtain ⟨ha0, haI, haI'⟩ := hI Ω ε X m hm u a hu ha
  obtain ⟨hb0, hbI, hbI'⟩ := hI Ω ε X m hm v b hv hb
  have hinL : ∀ g ∈ L.fixingSubgroup, g (io X u) = io X u ∧ g (io X v) = io X v := by
    intro g hg
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hg
    exact ⟨hg _ (IntermediateField.subset_adjoin _ _ (by simp)),
      hg _ (IntermediateField.subset_adjoin _ _ (by simp))⟩
  have hfix : ∀ g ∈ L.fixingSubgroup, g (a ^ m) = a ^ m ∧ g (b ^ m) = b ^ m := by
    intro g hg
    rw [ha, hb]
    exact hinL g hg
  obtain ⟨η₀, hlc, hcoc, hunr⟩ :=
    hS Ω (RatFunc Ω) (Kb X) m (zt X m) hζ L.fixingSubgroup hU a b ha0 hb0 haI haI' hbI hbI' hfix
  have hgeo : ∀ G : Kb X ≃ₐ[RatFunc Ω] Kb X, G ∈ GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) := by
    intro G
    unfold GlobalTheory.K4.geo
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨r, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact G.commutes r
  have hmem : ∀ G : Kb X ≃ₐ[RatFunc Ω] Kb X, G (io X u) = io X u → G (io X v) = io X v →
      G ∈ GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) ⊓ L.fixingSubgroup := by
    intro G hu' hv'
    refine Subgroup.mem_inf.mpr ⟨hgeo G, ?_⟩
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    have e := IntermediateField.adjoin_algHom_ext (RatFunc Ω)
      (φ₁ := (G.toAlgHom).comp L.val) (φ₂ := L.val) (by
        rintro x (rfl | rfl)
        · exact hu'
        · exact hv')
    exact AlgHom.congr_fun e ⟨y, hy⟩
  obtain ⟨B, hB⟩ := hL (RatFunc Ω) (Kb X) (ZMod m) _ (by
    have : GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) ⊓ L.fixingSubgroup = L.fixingSubgroup :=
      inf_eq_right.mpr fun G _ => hgeo G
    rw [this]
    exact hU) η₀ hlc
  have hcomm : ∀ g : RingAut (Kb X),
      (∀ c : Ω, g (io X (algebraMap Ω X.K c)) = io X (algebraMap Ω X.K c)) →
      g (io X X.jK) = io X X.jK → ∀ r, g (φ r) = φ r := by
    intro g h1 h2
    have e : (g.toRingHom.comp φ).comp (algebraMap (Polynomial Ω) (RatFunc Ω)) =
        φ.comp (algebraMap (Polynomial Ω) (RatFunc Ω)) := by
      apply Polynomial.ringHom_ext
      · intro c
        show g (φ (algebraMap (Polynomial Ω) (RatFunc Ω) (Polynomial.C c))) =
          φ (algebraMap (Polynomial Ω) (RatFunc Ω) (Polynomial.C c))
        rw [hφ]
        show g (io X (Polynomial.aeval X.jK (Polynomial.C c))) = io X (Polynomial.aeval X.jK (Polynomial.C c))
        rw [Polynomial.aeval_C]
        exact h1 c
      · show g (φ (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)) =
          φ (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)
        rw [hφ]
        show g (io X (Polynomial.aeval X.jK Polynomial.X)) = io X (Polynomial.aeval X.jK Polynomial.X)
        rw [Polynomial.aeval_X]
        exact h2
    have e2 := IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial Ω)) e
    intro r
    exact RingHom.congr_fun e2 r
  have hk : ∀ (g : RingAut (Kb X)) (G : Kb X ≃ₐ[RatFunc Ω] Kb X), (∀ x, G x = g x) →
      ∀ x : Kb X, x ≠ 0 → g (x ^ m) = x ^ m → ka X m x g = GlobalTheory.NeedB.kum (zt X m) x G := by
    intro g G hG x hx0 hxm
    obtain ⟨i, hi, huniq⟩ := existsUnique_eq_primitiveRoot_pow_mul_of_pow_eq (c := g x) hζ hx0 (by rw [← map_pow, hxm])
    unfold ka lg GlobalTheory.NeedB.kum
    rw [hG, dif_pos ⟨i, hi⟩]
    exact (huniq _ (Classical.epsilon_spec (p := fun j : ZMod m => g x = zt X m ^ j.val * x) ⟨i, hi⟩)).trans
      (huniq _ (Exists.choose_spec (⟨i, hi⟩ : ∃ j : ZMod m, g x = zt X m ^ j.val * x))).symm
  classical
  refine ⟨fun g => if hg : ∀ r, g (φ r) = φ r then η₀ (AlgEquiv.ofRingEquiv (f := g) hg) else 0,
    ?_, ?_, ?_⟩
  · intro g h hg hh
    unfold InU at hg hh
    obtain ⟨g1, g2, g3, g4⟩ := hg
    obtain ⟨h1, h2, h3, h4⟩ := hh
    have cg := hcomm g g1 g2
    have ch := hcomm h h1 h2
    have cgh : ∀ r, (g * h) (φ r) = φ r := fun r => by
      show g (h (φ r)) = φ r
      rw [ch, cg]
    have hGH : AlgEquiv.ofRingEquiv (f := g * h) cgh =
        AlgEquiv.ofRingEquiv (f := g) cg * AlgEquiv.ofRingEquiv (f := h) ch := by
      ext x
      rfl
    simp only [dif_pos cg, dif_pos ch, dif_pos cgh]
    rw [hGH, hk g (AlgEquiv.ofRingEquiv (f := g) cg) (fun _ => rfl) a ha0 (by rw [ha]; exact g3),
      hk h (AlgEquiv.ofRingEquiv (f := h) ch) (fun _ => rfl) b hb0 (by rw [hb]; exact h4)]
    exact hcoc _ (hmem _ g3 g4) _ (hmem _ h3 h4)
  · unfold LC
    refine ⟨B, ?_⟩
    intro h h' hh hh' hBB
    unfold InD at hh hh'
    have ch := hcomm h (fun c => hh _) (hh _)
    have ch' := hcomm h' (fun c => hh' _) (hh' _)
    simp only [dif_pos ch, dif_pos ch']
    exact hB _ (hmem _ (hh u) (hh v)) _ (hmem _ (hh' u) (hh' v)) hBB
  · unfold Unr
    intro B h hY hh hin
    unfold InD at hh
    unfold Tower.OverY at hY
    have ch := hcomm h (fun c => hh _) (hh _)
    simp only [dif_pos ch]
    refine (hunr (AlgEquiv.ofRingEquiv (f := h) ch) (hmem _ (hh u) (hh v)) B ?_ hin).1
    intro p
    show io X (Polynomial.aeval X.jK p) ∈ B
    have : Polynomial.aeval X.jK p ∈ B.comap (io X) := by
      refine Polynomial.induction_on p (fun c => ?_) (fun p q hp hq => ?_) (fun n c _ => ?_)
      · rw [Polynomial.aeval_C]
        exact hY.1 c
      · rw [map_add]
        exact add_mem hp hq
      · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        exact mul_mem (hY.1 c) (pow_mem hY.2 _)
    exact this

theorem etaEx : EtaEx := etaEx_of (GlobalTheory.K4.thmA_on_open_geo GlobalTheory.KummerCob.thmA) alg integ lcFin

end UpperTheory.V.Z.Kato.Sym.PE
end
