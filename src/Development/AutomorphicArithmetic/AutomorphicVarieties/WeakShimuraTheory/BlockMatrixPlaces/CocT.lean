import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.RedMem
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeqEx

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl.UnramifiedCardinality

variable {k D M : Type} [CommRing k] [Group D] [AddCommGroup M] [Module k M]

private def NI (ρ : Representation k D M) (I : Subgroup D) : Submodule k M where
  carrier := {m | ∀ s ∈ I, ρ s m = m}
  zero_mem' := fun s _ => map_zero _
  add_mem' := fun {a b} ha hb s hs => by rw [map_add, ha s hs, hb s hs]
  smul_mem' c a ha s hs := by rw [map_smul, ha s hs]

private theorem NI_stable (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (g : D) {m : M}
    (hm : m ∈ NI ρ I) : ρ g m ∈ NI ρ I := by
  intro s hs
  have h1 := hm (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹)
  calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
    _ = ρ g m := by rw [h1]

private theorem inv_apply (ρ : Representation k D M) (g : D) (m : M) : ρ g⁻¹ (ρ g m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem apply_inv (ρ : Representation k D M) (g : D) (m : M) : ρ g (ρ g⁻¹ m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable [TopologicalSpace D] [IsTopologicalGroup D]

private theorem all_of_closed {I : Subgroup D} {σ : D}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup D) (hH : IsClosed (H : Set D))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : D) : g ∈ H := by
  have := Subgroup.topologicalClosure_minimal (I ⊔ Subgroup.zpowers σ)
    (sup_le hI ((Subgroup.zpowers_le).2 hσ)) hH
  rw [hd] at this
  exact this (Subgroup.mem_top g)

private theorem exists_hom {E : Type} [Group E] [Finite E] {I : Subgroup D} {φ : D}
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) (e : E) :
    ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ w φ = e := by
  have hn : 0 < orderOf e := orderOf_pos e
  haveI : NeZero (orderOf e) := ⟨hn.ne'⟩
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf e) hn
  let f : Multiplicative (ZMod (orderOf e)) →* E :=
    MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by
      intro a b
      simp only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])
  have hf1 : f (Multiplicative.ofAdd 1) = e := by
    show e ^ (1 : ZMod (orderOf e)).val = e
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  refine ⟨f.comp d, hdl.comp f, fun s hs => by simp [hdI s hs], ?_⟩
  show f (d φ) = e
  rw [hdφ, hf1]

variable [TopologicalSpace M] [DiscreteTopology M]

private theorem exists_cocycle [Finite M] (ρ : Representation k D M) (hρ : ContAction ρ) {I : Subgroup D} [I.Normal] {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) {x : M} (hx : x ∈ NI ρ I) :
    ∃ z ∈ Z1 ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  let e : Equiv.Perm (NI ρ I) :=
    { toFun := fun m => ⟨x + ρ φ m, add_mem hx (NI_stable ρ I φ m.2)⟩
      invFun := fun m => ⟨ρ φ⁻¹ (m - x), NI_stable ρ I _ (sub_mem m.2 hx)⟩
      left_inv := fun m => Subtype.ext (by simp only [add_sub_cancel_left, inv_apply])
      right_inv := fun m => Subtype.ext (by simp only [apply_inv, add_sub_cancel]) }
  obtain ⟨w, hw, hwI, hwφ⟩ := exists_hom hd e
  have hc : ∀ m : NI ρ I, Continuous fun g => ((w g m : NI ρ I) : M) := fun m =>
    (hw.comp fun σ : Equiv.Perm (NI ρ I) => ((σ m : NI ρ I) : M)).continuous
  let H : Subgroup D :=
    { carrier := {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      mul_mem' := fun {a b} ha hb m m' => by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha, hb, Module.End.mul_apply]
      one_mem' := fun m m' => by simp
      inv_mem' := fun {a} ha m m' => by
        have h1 := ha (w a⁻¹ m) (w a⁻¹ m')
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Equiv.Perm.one_apply, Equiv.Perm.one_apply] at h1
        rw [h1, inv_apply] }
  have hH : ∀ g, g ∈ H := by
    refine all_of_closed hcl H ?_ (fun s hs m m' => ?_) (fun m m' => ?_)
    · change IsClosed {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun m => isClosed_iInter fun m' => isClosed_eq ((hc m).sub (hc m'))
        (Continuous.comp (f := fun g : D => (g, (m : M) - m')) hρ (by fun_prop))
    · rw [hwI s hs, (sub_mem m.2 m'.2 : _ ∈ NI ρ I) s hs]
      rfl
    · rw [hwφ, map_sub]
      change x + ρ φ m - (x + ρ φ m') = _
      abel
  refine ⟨fun g => ((w g 0 : NI ρ I) : M), ⟨hc 0, fun g h => ?_⟩, fun s hs => ?_, ?_⟩
  · have h1 := hH g (w h 0) 0
    rw [Submodule.coe_zero, sub_zero] at h1
    simp only [map_mul, Equiv.Perm.mul_apply]
    rw [← h1]
    abel
  · simp only [hwI s hs]
    rfl
  · simp only [hwφ]
    change x + ρ φ 0 = x
    simp

private theorem eq_zero_of (ρ : Representation k D M) {I : Subgroup D} {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) {d : D → M} (hd0 : d ∈ Z1 ρ)
    (hI : ∀ s ∈ I, d s = 0) (hφ : d φ = 0) (g : D) : d g = 0 := by
  have d1 : d 1 = 0 := by
    have := hd0.2 1 1
    simpa using this
  let H : Subgroup D :=
    { carrier := {g | d g = 0}
      mul_mem' := fun {a b} ha hb => by
        change d (a * b) = 0
        rw [hd0.2, show d a = 0 from ha, show d b = 0 from hb]
        simp
      one_mem' := d1
      inv_mem' := fun {a} ha => by
        have := hd0.2 a⁻¹ a
        rw [inv_mul_cancel, d1, show d a = 0 from ha] at this
        change d a⁻¹ = 0
        simpa using this.symm }
  exact all_of_closed hcl H (isClosed_eq hd0.1 continuous_const) hI hφ g

private def Z0 (ρ : Representation k D M) (I : Subgroup D) : Submodule k (Z1 ρ) where
  carrier := {z | ∀ s ∈ I, z.1 s = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb s hs => by
    change a.1 s + b.1 s = 0
    rw [ha s hs, hb s hs, add_zero]
  smul_mem' c a ha s hs := by
    change c • a.1 s = 0
    rw [ha s hs, smul_zero]

private theorem val_mem (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (z : Z0 ρ I) (g : D) :
    z.1.1 g ∈ NI ρ I := by
  intro s hs
  have h1 := z.1.2.2 s g
  have h2 := z.1.2.2 g (g⁻¹ * s * g)
  rw [z.2 s hs, zero_add] at h1
  rw [z.2 (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹), map_zero, add_zero,
    show g * (g⁻¹ * s * g) = s * g by group] at h2
  rw [← h1, h2]

private theorem card_range_ker {k A B : Type} [CommRing k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) :
    Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

end UpperTheory.V.Ws.Bl.UnramifiedCardinality

open UpperTheory.V.Ws.Bl.UnramifiedCardinality in
theorem UpperTheory.V.Ws.Bl.urCard :
    ∀ (R D M : Type) [CommRing R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M), ContAction ρ → ∀ (I : Subgroup D) [I.Normal] (φ : D), (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
          (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) → Nat.card (H1ur ρ I) = Nat.card (H0 ρ) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ hρ I _ φ hcl hd
  let ev : Z0 ρ I →ₗ[k] NI ρ I :=
    { toFun := fun z => ⟨z.1.1 φ, val_mem ρ I z φ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    refine ⟨(injective_iff_map_eq_zero ev).2 fun z hz => ?_, fun x => ?_⟩
    · exact Subtype.ext (Subtype.ext (funext
        (eq_zero_of ρ hcl z.1.2 z.2 (congrArg Subtype.val hz))))
    · obtain ⟨z, hz, hzI, hzφ⟩ := exists_cocycle ρ hρ hcl hd x.2
      exact ⟨⟨⟨z, hz⟩, hzI⟩, Subtype.ext hzφ⟩
  let E := LinearEquiv.ofBijective ev hev
  haveI : Finite (Z0 ρ I) := Finite.of_equiv _ E.symm.toEquiv
  let p : Z0 ρ I →ₗ[k] H1 ρ := (Submodule.mkQ _).comp (Z0 ρ I).subtype
  let δ : NI ρ I →ₗ[k] Z0 ρ I :=
    { toFun := fun m => ⟨⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs => sub_eq_zero.2 (m.2 s hs)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (map_add (d0 ρ) _ _))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (map_smul (d0 ρ) _ _)) }
  have h1 : LinearMap.range p = H1ur ρ I := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun s => ?_⟩)
      rw [map_zero, sub_zero]
      exact z.2 s s.2
    · intro c hc
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hc)
      refine ⟨⟨z - ⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs =>
        sub_eq_zero.2 (show z.1 s = d0 ρ m s from hm ⟨s, hs⟩)⟩, ?_⟩
      refine (Submodule.Quotient.eq _).2 ?_
      rw [Submodule.subtype_apply, sub_sub_cancel_left]
      exact neg_mem ⟨m, rfl⟩
  have h2 : LinearMap.range δ = LinearMap.ker p := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩
    · intro z hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)
      refine ⟨⟨m, fun s hs => sub_eq_zero.1 ((hm s).symm.trans (z.2 s hs))⟩, ?_⟩
      exact Subtype.ext (Subtype.ext (funext fun g => (hm g).symm))
  have h3 : (LinearMap.ker δ).map (NI ρ I).subtype = H0 ρ := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩ g
      exact sub_eq_zero.1 (congrFun (congrArg (fun z : Z0 ρ I => z.1.1) hm) g)
    · intro m hm
      exact ⟨⟨m, fun s _ => hm s⟩, Subtype.ext (Subtype.ext (funext fun g => sub_eq_zero.2 (hm g))), rfl⟩
  have a1 := card_range_ker p
  have a2 := card_range_ker δ
  have a3 : Nat.card (Z0 ρ I) = Nat.card (NI ρ I) := Nat.card_congr E.toEquiv
  have a4 : Nat.card (H0 ρ) = Nat.card (LinearMap.ker δ) := by
    rw [← h3]
    exact (Nat.card_congr (Submodule.equivMapOfInjective _ (NI ρ I).injective_subtype _).toEquiv).symm
  have a5 : 0 < Nat.card (LinearMap.ker p) := Nat.card_pos
  rw [h2, ← a3, a1, mul_comm] at a2
  rw [← h1, a4]
  exact Nat.eq_of_mul_eq_mul_right a5 a2
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.plusCard :
    LocalFiniteness → LocalEulerChar → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) M), 0 < r → IsPlaceOver B v → ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ContAction ρ →
          ∀ P : Submodule (ZMod (l ^ r)) M, (∀ h, ∀ x ∈ P, ρ h x ∈ P) → (∃ s, Function.Bijective fun x => ρ s x - x) →
          ∃ L : Submodule (ZMod (l ^ r)) (H1 ρ), Nat.card P ≤ Nat.card L ∧ ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ L → ∃ y, ∀ h, z.1 h - (ρ h y - y) ∈ P := by
  intro hFin hEul Ω _ _ _ l _ r M _ _ _ _ _ B v ρ hr hB hl hc P hP hs
  let ρP : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) P :=
    { toFun := fun h => (ρ h).restrict (fun x hx => hP h x hx)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp }
  have hρP : ∀ h (x : P), ((ρP h x : P) : M) = ρ h x := fun _ _ => rfl
  have hcP : ContAction ρP := by
    have h1 : Continuous fun p : Dec (F := ℚ) B × P => ρ p.1 (p.2 : M) :=
      hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact continuous_induced_rng.2 h1
  obtain ⟨hH0, hH1, hH2, -⟩ := hFin ℚ Ω l r P B ρP v hr hB hcP
  have hE := (hEul ℚ Ω l r P B ρP v hr hB hcP).1 hl
  have hdeg : 0 < locDeg v := by
    unfold locDeg
    exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : Nat.card P ≤ Nat.card (H1 ρP) := by
    rw [hE]
    have a0 : 0 < Nat.card (H0 ρP) := Nat.card_pos
    have a2 : 0 < Nat.card (H2 ρP) := Nat.card_pos
    calc Nat.card P ≤ Nat.card P ^ locDeg v := Nat.le_self_pow hdeg.ne' _
      _ ≤ Nat.card (H0 ρP) * Nat.card (H2 ρP) * Nat.card P ^ locDeg v :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos a0 a2)
  have hu : Continuous (P.subtype : P → M) := continuous_subtype_val
  have heq : ∀ (g : Dec (F := ℚ) B) (m : P), P.subtype (ρP g m) = ρ g (P.subtype m) := fun _ _ => rfl
  let φ := mapH1 ρP ρ P.subtype hu heq
  obtain ⟨s, hsb⟩ := hs
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    rw [Submodule.Quotient.mk_eq_zero]
    have hw' : (φ (Submodule.Quotient.mk w)) = 0 := hw
    simp only [φ, mapH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype] at hw'
    rw [mem_coboundaries1] at hw'
    obtain ⟨m, hm⟩ := hw'
    have hm' : ∀ g, ((w.1 g : P) : M) = ρ g m - m := fun g => hm g
    have hmP : m ∈ P := by
      obtain ⟨q, hq⟩ : ∃ q : P, ρP s q - q = w.1 s := by
        have hinjP : Function.Injective fun q : P => ρP s q - q := by
          intro a b hab
          apply Subtype.ext
          apply hsb.1
          have := congrArg Subtype.val hab
          simpa [hρP] using this
        exact (Finite.injective_iff_surjective.1 hinjP) (w.1 s)
      have h1 : ρ s (q : M) - q = ρ s m - m := by
        have := congrArg Subtype.val hq
        simp only [AddSubgroupClass.coe_sub, hρP] at this
        rw [this, hm' s]
      have := hsb.1 h1
      rw [← this]
      exact q.2
    rw [Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨⟨m, hmP⟩, fun g => ?_⟩
    apply Subtype.ext
    rw [hm' g]
    rfl
  refine ⟨LinearMap.range φ, ?_, ?_⟩
  · calc Nat.card P ≤ Nat.card (H1 ρP) := hle
      _ = Nat.card (LinearMap.range φ) := Nat.card_congr (LinearEquiv.ofInjective φ hinj).toEquiv
  · intro z hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hz
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    simp only [φ, mapH1, Submodule.mapQ_apply] at hw
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hw
    obtain ⟨y, hy⟩ := hw
    refine ⟨-y, fun h => ?_⟩
    have h1 := hy h
    have h2 : ((cocycles1MapOfEquivariant ρP ρ P.subtype hu heq w : Z1 ρ) : _ → M) h = (w.1 h : M) := rfl
    simp only [Submodule.coe_sub, Pi.sub_apply, h2] at h1
    have h3 : z.1 h - (ρ h (-y) - -y) = (w.1 h : M) := by
      rw [map_neg]
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    rw [h3]
    exact (w.1 h).2
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem card_one_of {R N : Type} [Ring R] [AddCommGroup N] [Module R N] (P : Submodule R N)
    (h : ∀ x ∈ P, x = 0) : Nat.card P = 1 := by
  haveI : Subsingleton P := ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩

theorem UpperTheory.V.Ws.Bl.gwIneq :
    GlobalFiniteness → GreenbergWiles → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), 0 < r → l ≠ 2 → ContainsAbove S l → ContAction ρ →
          ∀ c : G ℚ Ω, IsCC c → (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ (v0 : S) (s : G ℚ Ω), s ∈ Dec (F := ℚ) (Av v0) → cycZ ℚ Ω l s = 1 → (Function.Bijective fun x => ρ (toGS Ω _ s) x - x) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card (L v)) →
          Nat.card (L v0) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := by
  intro hGF hGW Ω _ _ _ l _ r M _ _ _ _ _ S ρ hr hl2 hS hρ c hc hcneg Av hAv v0 s hsD hsz hsbij L hL
  have hcop : Nat.Coprime 2 (l ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two (Fact.out)).mpr (Ne.symm hl2))
  have hinv : ∀ m : M, m = -m → m = 0 := by
    intro m hm
    set u := ZMod.unitOfCoprime 2 hcop
    have hu : (u : ZMod (l ^ r)) = 2 := by simp [u]
    have h2 : (2 : ZMod (l ^ r)) • m = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hm]
      exact add_neg_cancel m
    calc m = ((u⁻¹ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • ((u : ZMod (l ^ r)) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu, h2, smul_zero]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := r) hS
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w c := by
    intro w _
    obtain ⟨j, hj⟩ := hc
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have key := hGW ℚ Ω l r M S ρ hr hl2 hS hρ μ hμ Av hAv (fun _ => c) hcc L
  have hμs : μ (toGS Ω _ s) = 1 := by
    have h := congrArg (fun f => f s) hμ
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    simp [cycMod, hsz]
  have htw : Nat.card (H0 (twDual μ ρ)) = 1 := by
    refine card_one_of _ (fun φ hφ => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ φ).mp hφ (toGS Ω _ s)
    apply TDual.ext
    intro m
    obtain ⟨x, rfl⟩ := hsbij.2 m
    have hx : φ (ρ (toGS Ω _ s) x) = φ x := by
      have h := congrArg (fun ψ : TDual (ZMod (l ^ r)) M => ψ (ρ (toGS Ω _ s) x)) hfix
      simp only [twDual_apply, hμs, Units.val_one, one_mul] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hsub : (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x - x) =
        (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x) - (φ : Module.Dual (ZMod (l ^ r)) M) x :=
      LinearMap.map_sub _ _ _
    show φ (ρ (toGS Ω _ s) x - x) = 0
    exact hsub.trans (by erw [hx]; exact sub_self _)
  have harch : archH0Card S ρ (fun _ => c) = 1 := by
    have h0 : InfinitePlace.nrComplexPlaces ℚ = 0 := by simp
    unfold archH0Card
    rw [h0, pow_zero, mul_one]
    refine Finset.prod_eq_one (fun w _ => ?_)
    haveI : Subsingleton {m : M // ρ (toGS Ω _ c) m = m} :=
      ⟨fun a b => Subtype.ext (by
        have ha := hinv a.1 (by rw [← hcneg a.1, a.2])
        have hb := hinv b.1 (by rw [← hcneg b.1, b.2])
        rw [ha, hb])⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, map_zero _⟩⟩⟩
  have hv0 : Nat.card (H0 (ρ.comp (locFam S Av v0))) = 1 := by
    refine card_one_of _ (fun m hm => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).mp hm ⟨s, hsD⟩
    have hfix' : ρ (toGS Ω _ s) m = m := hfix
    apply hsbij.1
    show ρ (toGS Ω _ s) m - m = ρ (toGS Ω _ s) 0 - 0
    rw [hfix', sub_self, map_zero, sub_self]
  classical
  rw [htw, harch, mul_one, mul_one] at key
  obtain ⟨-, hH1, -, -⟩ := hGF ℚ Ω l r M S ρ hr hS hρ
  have hSelpos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hH0pos : ∀ v, 0 < Nat.card (H0 (ρ.comp (locFam S Av v))) := fun v => Nat.card_pos
  have hP := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Finset.mem_univ v0)
  have hQ := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (L v)) (Finset.mem_univ v0)
  simp only at hP hQ
  rw [hv0, one_mul] at hP
  set P' := ∏ v ∈ Finset.univ.erase v0, Nat.card (H0 (ρ.comp (locFam S Av v)))
  set Q' := ∏ v ∈ Finset.univ.erase v0, Nat.card (L v)
  have hP'pos : 0 < P' := Finset.prod_pos (fun v _ => hH0pos v)
  have hPQ : P' ≤ Q' := Finset.prod_le_prod (fun v _ => Nat.zero_le _)
    (fun v hv => hL v (Finset.ne_of_mem_erase hv))
  rw [← hP, ← hQ] at key
  set a := Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  set b := Nat.card (Sel (twDual μ ρ) (locFam S Av) _ (perpCond μ ρ (locFam S Av) _ L))
  set h0 := Nat.card (H0 ρ)
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · rw [hb, zero_mul, zero_mul] at key
      exact absurd key (Nat.mul_pos hSelpos hP'pos).ne'
    · exact hb
  have hh0 : 0 < h0 := Nat.card_pos
  have h1 : Nat.card (L v0) * Q' ≤ a * P' := by
    rw [key]
    calc Nat.card (L v0) * Q' ≤ (b * h0) * (Nat.card (L v0) * Q') :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos hbpos hh0)
      _ = _ := rfl
  have h2 : Nat.card (L v0) * P' ≤ a * P' :=
    le_trans (Nat.mul_le_mul_left _ hPQ) h1
  exact Nat.le_of_mul_le_mul_right h2 hP'pos
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem exists_norm {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (hρ : ContAction ρ)
    (h2 : Function.Surjective fun m : M => m + m) (c : Γ) (hc : ∀ m, ρ c m = -m) (x : H1 ρ) :
    ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 c = 0 := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := h2 (-(z0.1 c))
  have hB : d0 ρ m ∈ Z1 ρ := coboundaries_le_cocycles ρ hρ (LinearMap.mem_range_self _ m)
  refine ⟨z0 - ⟨d0 ρ m, hB⟩, ?_, ?_⟩
  · rw [Submodule.Quotient.eq, Submodule.mem_comap, sub_sub_cancel_left, map_neg]
    exact Submodule.neg_mem _ ⟨m, rfl⟩
  · show z0.1 c - d0 ρ m c = 0
    rw [amitsur_d0_apply, hc]
    have hm' : m + m = -(z0.1 c) := hm
    calc z0.1 c - (-m - m) = z0.1 c + (m + m) := by abel
      _ = 0 := by rw [hm']; abel

theorem UpperTheory.V.Ws.Bl.selToZc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → (Function.Bijective fun m : M => m + m) →
          ∀ c : G ℚ Ω, (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ v0 : S, ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal → ∀ (P : Set M) (K : Subgroup (G ℚ Ω)), (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → L v ≤ H1ur (ρ.comp (locFam S Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) →
          (∀ z : Z1 (ρ.comp (locFam S Av v0)), (Submodule.Quotient.mk z : H1 (ρ.comp (locFam S Av v0))) ∈ L v0 → ∃ y, ∀ h, z.1 h - (ρ (locFam S Av v0 h) y - y) ∈ P) →
          ∃ f : Sel ρ (locFam S Av) (continuous_locFam S Av) L → Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P, Function.Injective f := by
  intro Ω _ _ _ l _ R M _ _ _ _ _ S ρ hρ hbij c hcneg Av hAv v0 hlv0 P K hK L hL hP
  have hex : ∀ x : H1 ρ, ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 (toGS Ω _ c) = 0 :=
    fun x => exists_norm ρ hρ hbij.2 (toGS Ω _ c) hcneg x
  have hA : ∀ x : H1 ρ, x ∈ Sel ρ (locFam S Av) (continuous_locFam S Av) L → ∀ z : Z1 ρ,
      (Submodule.Quotient.mk z : H1 ρ) = x → z.1 (toGS Ω _ c) = 0 →
      (fun g => z.1 (toGS Ω _ g)) ∈ Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P := by
    intro x hx z hzx hzc
    subst hzx
    have hcoc : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
    have hz1 : z.1 1 = 0 := by
      have h := hcoc 1 1
      rw [one_mul, map_one, Module.End.one_apply] at h
      simpa using h
    have hmemv : ∀ v, (Submodule.Quotient.mk (restrictCocycles1 ρ (locFam S Av v) (continuous_locFam S Av v) z) :
        H1 (ρ.comp (locFam S Av v))) ∈ L v := fun v => (mem_Sel _ _ _ _ _).mp hx v
    obtain ⟨y, hy⟩ := hP _ (hmemv v0)
    refine ⟨y, ⟨?_, ?_, hzc, ?_, ?_⟩⟩
    · exact ((IsLocallyConstant.iff_continuous _).mpr ((mem_Z1_iff_cocycle _ _).mp z.2).1).comp_continuous
        continuous_quot_mk
    · intro g h
      show z.1 (toGS Ω _ (g * h)) = z.1 (toGS Ω _ g) + ρ (toGS Ω _ g) (z.1 (toGS Ω _ h))
      rw [map_mul]
      exact hcoc _ _
    · rintro g ⟨hgK, A, hAl, hgA⟩
      show z.1 (toGS Ω _ g) = 0
      by_cases hAtop : A = ⊤
      · subst hAtop
        rw [(UpperTheory.V.Kum.placeDict ℚ Ω).1, Subgroup.mem_bot] at hgA
        rw [hgA, map_one, hz1]
      obtain ⟨v, hAv'⟩ := (UpperTheory.V.Kum.placeDict ℚ Ω).2.1 A hAtop
      by_cases hvS : v ∈ S
      · set w : S := ⟨v, hvS⟩
        have hne : w ≠ v0 := by
          intro hw
          apply hAl
          have h := (hAv' (l : 𝓞 ℚ)).mpr (by rw [show v = v0.1 from congrArg Subtype.val hw]; exact hlv0)
          simpa using h
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hAv w) hAv'
        rw [← hσ] at hgA
        have hgA' : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (Av w) := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hgA
        have hur := hL w hne (hmemv w)
        rw [H1ur, LinearMap.mem_ker] at hur
        have hur' := (Submodule.Quotient.mk_eq_zero _).mp hur
        rw [Submodule.mem_comap] at hur'
        obtain ⟨m, hm⟩ := hur'
        have hj := congrFun hm ⟨⟨σ⁻¹ * g * σ, Ine_le_Dec _ hgA'⟩, hgA'⟩
        rw [amitsur_d0_apply] at hj
        have hconj : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = 0 := by
          have hj' : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = ρ (toGS Ω _ (σ⁻¹ * g * σ)) m - m := hj.symm
          rw [hj']
          rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
            show ρ (toGS Ω _ g) (ρ (toGS Ω _ σ) m) = ρ (toGS Ω _ σ) m from hK g hgK _,
            ← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel, map_one, Module.End.one_apply, sub_self]
        set a := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ
        set b := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
        have hb : ∀ m, ρ b m = m := hK g hgK
        rw [map_mul, map_mul, map_inv] at hconj
        have e1 := hcoc (a⁻¹ * b) a
        have e2 := hcoc a⁻¹ b
        have e3 := hcoc a⁻¹ a
        rw [inv_mul_cancel, hz1] at e3
        rw [map_mul, Module.End.mul_apply, hb, e2, hconj] at e1
        have hinv0 : ρ a⁻¹ (z.1 b) = 0 := by
          have : (0 : M) = ρ a⁻¹ (z.1 b) + (z.1 a⁻¹ + ρ a⁻¹ (z.1 a)) := by rw [e1]; abel
          rw [← e3, add_zero] at this
          exact this.symm
        have : z.1 b = ρ a (ρ a⁻¹ (z.1 b)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [this, hinv0, map_zero]
      · have hgN : g ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) :=
          Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
            (Set.mem_iUnion₂.mpr ⟨v, hvS, Set.mem_iUnion₂.mpr ⟨A, hAv', hgA⟩⟩))
        rw [show toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g = 1 from (QuotientGroup.eq_one_iff g).mpr hgN, hz1]
    · intro h hh
      exact hy ⟨h, hh⟩
  choose zc hzc using hex
  refine ⟨fun x => ⟨fun g => (zc x.1).1 (toGS Ω _ g), hA x.1 x.2 (zc x.1) (hzc x.1).1 (hzc x.1).2⟩, ?_⟩
  intro x x' hxx
  have hfun : (fun g => (zc x.1).1 (toGS Ω _ g)) = (fun g => (zc x'.1).1 (toGS Ω _ g)) :=
    congrArg Subtype.val hxx
  have hz : zc x.1 = zc x'.1 := by
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) q
    exact congrFun hfun g
  apply Subtype.ext
  rw [← (hzc x.1).1, ← (hzc x'.1).1, hz]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.placeSet :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (B : ValuationSubring Ω), (∀ p ∈ S, p.Prime) → l ∈ S → B.valuation (l : Ω) < 1 →
          ∃ (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (Av : S' → ValuationSubring Ω) (v0 : S'), ContainsAbove S' l ∧ (∀ v, IsPlaceOver (Av v) v.1) ∧ Av v0 = B ∧ ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal ∧
            ∀ K : Subgroup (G ℚ Ω), K.Normal → IsClosed (K : Set (G ℚ Ω)) → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ K := by
  intro Ω _ _ _ l hl S B hS hlS hB
  classical
  have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} := by
    have e : {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =
        ⋃ p ∈ (S : Set ℕ), {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 ℚ)}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [e]
    refine S.finite_toSet.biUnion fun p hp => Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (hS p hp).ne_zero
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places ℚ Ω l B
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := (h3 w hw).1 hB
  have hex : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ (v = w → A = B) := by
    intro v
    by_cases e : v = w
    · exact ⟨B, e ▸ hw, fun _ => rfl⟩
    · obtain ⟨A, hA⟩ := (exists_isPlaceOver Ω v : ∃ A : ValuationSubring Ω, IsPlaceOver A v)
      exact ⟨A, hA, fun h => absurd h e⟩
  choose f hf hf' using hex
  refine ⟨hfin.toFinset, fun v => f v.1, ⟨w, hfin.mem_toFinset.2 ⟨l, hlS, hlw⟩⟩,
    fun v hv => hfin.mem_toFinset.2 ⟨l, hlS, hv⟩, fun v => hf v.1, hf' w rfl, hlw, fun K hK hc hI => ?_⟩
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  refine hI A (fun p hp h => hv ?_) hg
  refine Finset.mem_coe.2 (hfin.mem_toFinset.2 ⟨p, hp, (hA ((p : ℕ) : 𝓞 ℚ)).1 ?_⟩)
  simpa using h
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]

private theorem coc_one {ρ : Representation R Γ M} {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) : z 1 = 0 := by
  have h := hz 1 1
  simpa using h

private def killSub (ρ : Representation R Γ M) {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) : Subgroup Γ where
  carrier := {g | ρ g = 1 ∧ z g = 0}
  one_mem' := ⟨map_one ρ, coc_one hz⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul, ha, hb, one_mul], by rw [hz, ha', hb', map_zero, add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have : ρ (a * a⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
      rwa [map_mul, ha, one_mul] at this
    refine ⟨h1, ?_⟩
    have h := hz a a⁻¹
    rw [mul_inv_cancel, coc_one hz, ha', ha] at h
    simpa using h.symm

private theorem killSub_normal (ρ : Representation R Γ M) {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) :
    (killSub ρ hz).Normal where
  conj_mem := by
    rintro g ⟨hg, hg'⟩ h
    refine ⟨by rw [map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    have e := hz h h⁻¹
    rw [mul_inv_cancel, coc_one hz] at e
    rw [hz, hz, hg', map_zero, add_zero, map_mul, hg, mul_one]
    exact e.symm

variable [TopologicalSpace Γ]

private theorem killSub_closed (ρ : Representation R Γ M) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m) {z : Γ → M}
    (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (hl : IsLocallyConstant z) : IsClosed (killSub ρ hz : Set Γ) := by
  have e : (killSub ρ hz : Set Γ) = (⋂ m : M, {g | ρ g m = m}) ∩ {g | z g = 0} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact and_congr_left' LinearMap.ext_iff
  rw [e]
  exact IsClosed.inter (isClosed_iInter fun m => (hρ m).isClosed_fiber m) (hl.isClosed_fiber 0)

private theorem module_finite_z1_padicInt [TopologicalSpace M] [DiscreteTopology M] [Finite M] (ρ : Representation R Γ M) [Finite (H1 ρ)] :
    Finite (Z1 ρ) := by
  haveI : Finite (B1 ρ) := (Set.finite_range (d0 ρ)).to_subtype
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h))
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup := this
  haveI : Finite (Z1 ρ ⧸ ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup) := ‹Finite (H1 ρ)›
  exact Finite.of_addSubgroup_quotient ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup

end

theorem UpperTheory.V.Ws.Bl.zcFin :
    GlobalFiniteness → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → ∀ P : Set M, (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) P).Finite := by
  intro hGF Ω _ _ _ l _ S c s B hP R M _ _ _ _ ρ r hr hρ K hK hI P
  obtain ⟨S', -, -, hS, -, -, -, hN⟩ := UpperTheory.V.Ws.Bl.placeSet S B hP.prime hP.mem hP.ovl
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hr' : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  obtain ⟨inst⟩ : Nonempty (Module (ZMod (l ^ (r + 1))) M) := ⟨AddCommGroup.zmodModule hr'⟩
  have h0 : ∀ g h : G ℚ Ω, (0 : G ℚ Ω → M) (g * h) = (0 : G ℚ Ω → M) g + ρ g ((0 : G ℚ Ω → M) h) := by simp
  have hker : NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ killSub ρ h0 :=
    hN _ (killSub_normal ρ h0) (killSub_closed ρ hρ h0 (IsLocallyConstant.const 0)) fun A hA g hg => ⟨hK (hI A hA hg), rfl⟩
  let ρ' : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by rw [map_mul]; rfl }
  let ρS : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ' fun g hg => LinearMap.ext fun m => show ρ g m = m by rw [(hker hg).1]; rfl
  have hρS : ContAction ρS := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact (hρ m).continuous
  obtain ⟨-, f1, -⟩ := hGF ℚ Ω l (r + 1) M S' ρS r.succ_pos hS hρS
  haveI := f1
  haveI := module_finite_z1_padicInt ρS
  refine (Set.finite_range fun z : Z1 ρS => z.1 ∘ toGS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))).subset ?_
  rintro z ⟨y, hz⟩
  have hle : NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ killSub ρ hz.coc :=
    hN _ (killSub_normal ρ _) (killSub_closed ρ hρ _ hz.lc) fun A hA g hg =>
      ⟨hK (hI A hA hg), hz.kill g ⟨hI A hA hg, A, hA l hP.mem, hg⟩⟩
  let zS : GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) → M := Quotient.lift z fun a b hab => by
    have h := (hle (QuotientGroup.leftRel_apply.1 hab)).2
    have e := hz.coc a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h, map_zero, add_zero] at e
    exact e.symm
  refine ⟨⟨zS, hz.lc.continuous.quotient_lift _, fun x y => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hz.coc a b
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.gwCount :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → (∀ m, ρ c m = -m) → (Function.Bijective fun m => ρ s m - m) →
          ∀ P : Submodule R M, (∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P, ρ h x ∈ P) → Nat.card P ≤ Nat.card (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := by
  classical
  intro hC Ω _ _ _ l hl S c s B hP R M _ _ _ _ ρ r hr hlc K hK hun hc hs P hPs
  have hfin := zcFin hC.gf S c s B hP R M ρ r hr hlc K hK hun (P : Set M)
  haveI : Finite (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := hfin
  obtain ⟨S', Av, v0, hS', hAv, hB, hv0, hNS⟩ := placeSet (l := l) S B hP.prime hP.mem hP.ovl
  subst hB
  have hr1 : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr1
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hcl : IsClosed (ρ.ker : Set (G ℚ Ω)) := by
    have e : (ρ.ker : Set (G ℚ Ω)) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isClosed_iInter fun m => ((hlc m).isClopen_fiber m).1
  have hN := hNS ρ.ker inferInstance hcl fun A hA => (hun A hA).trans hK
  let ρ1 : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  let σ : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ1 fun g hg => LinearMap.ext fun m => show ρ g m = m by
      rw [show ρ g = 1 from hN hg]; rfl
  have hσ : ∀ g m, σ (toGS Ω _ g) m = ρ g m := fun _ _ => rfl
  have hcont : ContAction σ := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hlc m).continuous
  have hloc : ∀ v, ContAction (σ.comp (locFam S' Av v)) := fun v =>
    Continuous.comp (f := fun p : Dec (F := ℚ) (Av v) × M => (locFam S' Av v p.1, p.2)) hcont
      (((continuous_locFam S' Av v).comp continuous_fst).prodMk continuous_snd)
  let P' : Submodule (ZMod (l ^ (r + 1))) M := AddSubgroup.toZModSubmodule _ P.toAddSubgroup
  obtain ⟨L0, hL0, hL0'⟩ := plusCard hC.loc.lf hC.loc.le (r + 1) M (Av v0) v0.1 (σ.comp (locFam S' Av v0))
    r.succ_pos (hAv v0) hv0 (hloc v0) P' (fun h x hx => hPs h.1 h.2 x hx) ⟨⟨s, hP.dec⟩, hs⟩
  let L : LocCond σ (locFam S' Av) := Function.update
    (fun v => H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) v0 L0
  have hLv0 : L v0 = L0 := Function.update_self ..
  have hLv : ∀ v, v ≠ v0 →
      L v = H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v))) :=
    fun v hv => Function.update_of_ne hv ..
  have h1 := gwIneq hC.gf hC.gw (r + 1) M S' σ r.succ_pos hP.odd hS' hcont c hP.cc hc Av hAv v0 s hP.dec hP.cyc hs L
    fun v hv => by
      obtain ⟨φ, -, h1, h2⟩ := GC.decZhat ℚ Ω v.1 (Av v) (hAv v)
      rw [hLv v hv, urCard _ _ _ _ (hloc v) _ φ h1 h2]
  have h2 : Function.Bijective fun m : M => m + m := by
    refine Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero (AddMonoidHom.id M + AddMonoidHom.id M)).2 ?_)
    intro m hm
    have hm2 : 2 • m = 0 := by rw [two_smul]; exact hm
    have hco : Nat.Coprime 2 (l ^ r) :=
      ((Nat.coprime_primes Nat.prime_two hl.out).2 hP.odd.symm).pow_right _
    have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm2) (addOrderOf_dvd_of_nsmul_eq_zero (hr m))
    rw [hco.gcd_eq_one, Nat.dvd_one] at this
    exact AddMonoid.addOrderOf_eq_one_iff.1 this
  obtain ⟨f, hf⟩ := selToZc (l := l) _ M S' σ hcont h2 c hc Av hAv v0 hv0 (P : Set M) K
    (fun g hg m => show ρ g m = m by rw [show ρ g = 1 from hK hg]; rfl) L (fun v hv => (hLv v hv).le)
    (fun z hz => hL0' z (hLv0 ▸ hz))
  rw [hLv0] at h1
  exact hL0.trans (h1.trans (Nat.card_le_card_of_injective f hf))
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cardP :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (P : Submodule A T), (∀ (a : A) (x : T), a ≠ 0 → a • x ∈ P → x ∈ P) → P ≠ ⊥ →
          ∀ n, Finite (T ⧸ lev A T n) ∧ n ≤ Nat.card (P.map (lev A T n).mkQ) := by
  intro A _ _ _ _ T _ _ _ _ P hsat hP n
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hL : ∀ (k : ℕ) (z : T), z ∈ lev A T k ↔ ∃ t, ϖ ^ k • t = z := by
    intro k z
    show z ∈ maximalIdeal A ^ k • (⊤ : Submodule A T) ↔ _
    rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hfin : ∀ k, Finite (T ⧸ lev A T k) := by
    intro k
    have h1 : (maximalIdeal A).FG := IsNoetherian.noetherian _
    haveI : Finite (A ⧸ maximalIdeal A) := (inferInstance : Finite (ResidueField A))
    haveI := Ideal.finite_quotient_pow h1 k
    haveI : Finite (T ⧸ (⊤ : Submodule A T)) := inferInstance
    exact Submodule.finite_quotient_smul _ (Module.finite_def.mp inferInstance)
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hx : ∃ x ∈ P, x ∉ lev A T 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, ∀ z ∈ P, z ∈ lev A T k := by
      intro k
      induction k with
      | zero =>
        intro z _
        exact (hL 0 z).mpr ⟨z, by simp⟩
      | succ k ih =>
        intro z hz
        obtain ⟨t, rfl⟩ := (hL 1 z).mp (hcon z hz)
        have htP : t ∈ P := hsat _ _ (pow_ne_zero 1 hϖ0) hz
        obtain ⟨s, rfl⟩ := (hL k t).mp (ih t htP)
        exact (hL (k + 1) _).mpr ⟨s, by rw [smul_smul, ← pow_add, add_comm 1 k]⟩
    have hmem : y ∈ (⨅ i : ℕ, maximalIdeal A ^ i • (⊤ : Submodule A T)) :=
      Submodule.mem_iInf _ |>.mpr (fun i => hall i y hyP)
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hmem
    exact hy0 ((Submodule.mem_bot A).mp hmem)
  obtain ⟨x, hxP, hx1⟩ := hx
  refine ⟨hfin n, ?_⟩
  haveI := hfin n
  have key : ∀ i j : ℕ, i < j → j < n → ϖ ^ i • x - ϖ ^ j • x ∉ lev A T n := by
    intro i j hij hjn hmem
    obtain ⟨s, hs⟩ := (hL n _).mp hmem
    have e1 : ϖ ^ i • (ϖ ^ (n - i) • s) = ϖ ^ i • (x - ϖ ^ (j - i) • x) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega), hs, smul_sub, smul_smul,
        ← pow_add, Nat.add_sub_cancel' hij.le]
    have e2 : ϖ ^ (n - i) • s = x - ϖ ^ (j - i) • x :=
      smul_right_injective T (pow_ne_zero i hϖ0) e1
    apply hx1
    rw [hL 1]
    refine ⟨ϖ ^ (n - i - 1) • s + ϖ ^ (j - i - 1) • x, ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Nat.add_sub_cancel' (by omega : 1 ≤ n - i), Nat.add_sub_cancel' (by omega : 1 ≤ j - i),
      e2, sub_add_cancel]
  let f : Fin n → P.map (lev A T n).mkQ := fun i =>
    ⟨(lev A T n).mkQ (ϖ ^ (i : ℕ) • x), Submodule.mem_map_of_mem (P.smul_mem _ hxP)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h' : (lev A T n).mkQ (ϖ ^ (i : ℕ) • x) = (lev A T n).mkQ (ϖ ^ (j : ℕ) • x) :=
      congrArg Subtype.val hij
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h'
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd h' (key _ _ h j.2)
    · exact Fin.ext h
    · have h'' := (lev A T n).neg_mem h'
      rw [neg_sub] at h''
      exact absurd h'' (key _ _ h i.2)
  calc n = Nat.card (Fin n) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective f hf
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_lev_iff {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {T : Type} [AddCommGroup T]
    [Module A T] {t : A} (ht : Irreducible t) (n : ℕ) (x : T) : x ∈ lev A T n ↔ ∃ w, t ^ n • w = x := by
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht
  show x ∈ maximalIdeal A ^ n • (⊤ : Submodule A T) ↔ _
  rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem mem_of_bij {A : Type} [CommRing A] {T : Type} [AddCommGroup T] [Module A T] [Module.Finite A T]
    (f : T →ₗ[A] T) (hf : Function.Surjective f) (Q : Submodule A T) (hQ : Q ≤ Q.comap f) {y : T} (hy : f y ∈ Q) :
    y ∈ Q := by
  let g := Q.mapQ Q f hQ
  have hs : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨w, rfl⟩ := hf x
    exact ⟨Q.mkQ w, by simp [g]⟩
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hs
  have h0 : g (Q.mkQ y) = g 0 := by
    simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, map_zero]
    exact (Submodule.Quotient.mk_eq_zero Q).2 hy
  have h1 := hi h0
  simpa using h1

theorem UpperTheory.V.Ws.Bl.divStep :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → ∀ t : A, Irreducible t → ∀ n, ∀ z ∈ Zn ρ c N H P (n + 1), ¬ Prim z →
          ∃ z' ∈ Zn ρ c N H P n, ∀ g x, (lev A T n).mkQ x = z' g → (lev A T (n + 1)).mkQ (t • x) = z g := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL t ht n z hz hnp
  obtain ⟨y, hzy⟩ := hz
  have ht0 : t ≠ 0 := ht.ne_zero
  have hinjt : Function.Injective (fun x : T => t • x) := smul_right_injective T ht0
  have hlev := fun k x => mem_lev_iff (T := T) ht k x
  have hφ : lev A T n ≤ (lev A T (n + 1)).comap (t • LinearMap.id) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (hlev n x).1 hx
    rw [Submodule.mem_comap]
    refine (hlev (n + 1) _).2 ⟨w, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]
  let φ := (lev A T n).mapQ (lev A T (n + 1)) (t • LinearMap.id) hφ
  have hφmk : ∀ x, φ ((lev A T n).mkQ x) = (lev A T (n + 1)).mkQ (t • x) := fun x => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [hφmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨w, hw⟩ := (hlev (n + 1) _).1 ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (hlev n x).2 ⟨w, hinjt ?_⟩
    simp only
    rw [← hw, pow_succ', mul_smul]
  have hφP : ∀ a, φ a ∈ Submodule.map (lev A T (n + 1)).mkQ P →
      a ∈ Submodule.map (lev A T n).mkQ P := by
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    obtain ⟨q, hq, hqe⟩ := Submodule.mem_map.1 ha
    rw [hφmk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hqe
    obtain ⟨v, hv⟩ := (hlev (n + 1) _).1 hqe
    have hq' : t • (x + t ^ n • v) ∈ P := by
      have e : t • (x + t ^ n • v) = q := by
        rw [smul_add, ← mul_smul, ← pow_succ', hv]
        abel
      rw [e]
      exact hq
    have hxP := hL.sat t _ ht0 hq'
    refine Submodule.mem_map.2 ⟨x + t ^ n • v, hxP, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (hlev n _).2 ⟨v, by abel⟩
  have hφρ : ∀ g a, φ (modRep ρ n g a) = modRep ρ (n + 1) g (φ a) := by
    intro g a
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [modRep_mk, hφmk, hφmk, modRep_mk, LinearMap.map_smul (ρ g) t x]
  have hz1 : ∀ g, z g ∈ Submodule.map (lev A T (n + 1)).mkQ (lev A T 1) := by
    intro g
    by_contra hc
    exact hnp ⟨g, hc⟩
  have hrange : ∀ g, ∃ a, φ a = z g := by
    intro g
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 g)
    obtain ⟨w, rfl⟩ := (hlev 1 u).1 hu
    refine ⟨(lev A T n).mkQ w, ?_⟩
    rw [hφmk, ← hue, pow_one]
  choose z' hz' using hrange
  obtain ⟨s, hsH, hsb⟩ := hL.fr
  obtain ⟨y0, rfl⟩ := (lev A T (n + 1)).mkQ_surjective y
  have hle1 : lev A T (n + 1) ≤ lev A T 1 :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  have hy0 : y0 ∈ P ⊔ lev A T 1 := by
    let f : T →ₗ[A] T := ρ s - LinearMap.id
    have hfs : Function.Surjective f := hsb.2
    apply mem_of_bij f hfs
    · intro x hx
      rw [Submodule.mem_comap]
      show ρ s x - x ∈ _
      apply Submodule.sub_mem _ _ hx
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      refine Submodule.mem_sup.2 ⟨ρ s p, hL.stab s hsH p hp, ρ s q, ?_, (map_add _ _ _).symm⟩
      obtain ⟨w, rfl⟩ := (hlev 1 q).1 hq
      exact (hlev 1 _).2 ⟨ρ s w, (map_smul _ _ _).symm⟩
    · show ρ s y0 - y0 ∈ _
      have hloc : z s - (modRep ρ (n + 1) s ((lev A T (n + 1)).mkQ y0) - (lev A T (n + 1)).mkQ y0)
          ∈ Submodule.map (lev A T (n + 1)).mkQ P := hzy.loc s hsH
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hloc
      obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 s)
      rw [modRep_mk, ← hue, ← map_sub, ← map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hpe
      have e : ρ s y0 - y0 = ((p - (u - (ρ s y0 - y0))) + u) - p := by abel
      rw [e]
      apply Submodule.sub_mem _ _ (Submodule.mem_sup_left hp)
      apply Submodule.add_mem _ (Submodule.mem_sup_right (hle1 hpe)) (Submodule.mem_sup_right hu)
  obtain ⟨p0, hp0, q0, hq0, hpq⟩ := Submodule.mem_sup.1 hy0
  obtain ⟨w0, rfl⟩ := (hlev 1 q0).1 hq0
  subst hpq
  have hcomp : ⇑φ ∘ z' = z := funext hz'
  refine ⟨z', ⟨(lev A T n).mkQ w0, ?_⟩, ?_⟩
  · refine ⟨IsLocallyConstant.desc z' φ (by rw [hcomp]; exact hzy.lc) hφinj, ?_, ?_, ?_, ?_⟩
    · intro g h
      show z' (g * h) = z' g + modRep ρ n g (z' h)
      apply hφinj
      rw [hz', map_add, hφρ, hz', hz']
      exact hzy.coc g h
    · apply hφinj
      rw [hz', map_zero]
      exact hzy.cz
    · intro g hg
      apply hφinj
      rw [hz', map_zero]
      exact hzy.kill g hg
    · intro h hh
      show z' h - (modRep ρ n h ((lev A T n).mkQ w0) - (lev A T n).mkQ w0)
        ∈ Submodule.map (lev A T n).mkQ P
      apply hφP
      rw [map_sub, map_sub, hφρ, hz', hφmk]
      have hloc : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
          - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) ∈ Submodule.map (lev A T (n + 1)).mkQ P :=
        hzy.loc h hh
      have e : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (t • w0)) - (lev A T (n + 1)).mkQ (t • w0))
          = (z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
            - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))) + (lev A T (n + 1)).mkQ (ρ h p0 - p0) := by
        simp only [pow_one, map_add, map_sub, modRep_mk]
        abel
      rw [e]
      exact Submodule.add_mem _ hloc
        (Submodule.mem_map_of_mem (Submodule.sub_mem _ (hL.stab h hh p0 hp0) hp0))
  · intro g x hx
    rw [← hφmk, hx, hz']
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.primEx :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, n ≤ Nat.card (Zn ρ c N H P n)) → ∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL hfin hcard n hn
  by_contra hne
  push_neg at hne
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hA : ∀ k, ∀ z ∈ Zn ρ c N H P (n + k), ¬Prim z := by
    intro k
    induction k with
    | zero => exact hne
    | succ k ih =>
      intro z hz hpz
      obtain ⟨y, hy⟩ := hz
      have hr := redMem A T Γ ρ c N H P (n + k) z y hy
      exact ih _ ⟨_, hr.1⟩ (hr.2.1 hpz (by omega))
  have hB : ∀ k, Nat.card (Zn ρ c N H P (n + k + 1)) ≤ Nat.card (Zn ρ c N H P (n + k)) := by
    intro k
    haveI := (hfin (n + k)).to_subtype
    have key : ∀ z : Zn ρ c N H P (n + k + 1), ∃ z' : Zn ρ c N H P (n + k),
        ∀ g x, (lev A T (n + k)).mkQ x = z'.1 g → (lev A T (n + k + 1)).mkQ (t • x) = z.1 g := by
      intro z
      obtain ⟨z', hz', h⟩ := divStep A T Γ ρ c N H P hL t ht (n + k) z.1 z.2 (hA (k + 1) z.1 z.2)
      exact ⟨⟨z', hz'⟩, h⟩
    choose f hf using key
    refine Nat.card_le_card_of_injective f ?_
    intro z1 z2 h12
    apply Subtype.ext
    funext g
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (lev A T (n + k)) ((f z1).1 g)
    rw [← hf z1 g x hx, hf z2 g x (by rw [hx, h12])]
  have hC : ∀ k, Nat.card (Zn ρ c N H P (n + k)) ≤ Nat.card (Zn ρ c N H P n) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hB k).trans ih
  have h1 := hcard (n + (Nat.card (Zn ρ c N H P n) + 1))
  have h2 := hC (Nat.card (Zn ρ c N H P n) + 1)
  omega
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

open CategoryTheory in
private theorem seq_ex (S : ℕ → Type) (hf : ∀ n, Finite (S n)) (hn : ∀ n, Nonempty (S n)) (t : ∀ n, S (n + 1) → S n) :
    ∃ u : ∀ n, S n, ∀ n, t n (u (n + 1)) = u n :=
  _root_.UpperTheory.Reformulated.B.Qj7.seq_ex S hf hn t

theorem UpperTheory.V.Ws.Bl.compat :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), (∀ n, Finite (T ⧸ lev A T n)) → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z) →
          ∃ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) ∧ (∀ n g, redn A T n (z (n + 1) g) = z n g) ∧ (∀ n, redn A T n (y (n + 1)) = y n) ∧ Prim (z 1) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hT hZ hP
  let S : ℕ → Type := fun n =>
    {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) // IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}
  let t : ∀ n, S (n + 1) → S n := fun n p =>
    ⟨(fun g => redn A T n (p.1.1 g), redn A T n p.1.2),
      (redMem A T Γ ρ c N H P n _ _ p.2.1).1,
      (redMem A T Γ ρ c N H P n _ _ p.2.1).2.1 (p.2.2 n.succ_pos)⟩
  have hf : ∀ n, Finite (S n) := fun n => by
    have := hT n
    have h : ((Zn ρ c N H P n) ×ˢ (Set.univ : Set (T ⧸ lev A T n))).Finite := (hZ n).prod Set.finite_univ
    exact (h.subset (fun p (hp : IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)) => ⟨⟨p.2, hp.1⟩, trivial⟩)).to_subtype
  have hn : ∀ n, Nonempty (S n) := fun n => by
    obtain ⟨z, ⟨y, hz⟩, hp⟩ := hP (n + 1) n.succ_pos
    exact ⟨t n ⟨(z, y), hz, fun _ => hp⟩⟩
  obtain ⟨u, hu⟩ := seq_ex S hf hn t
  exact ⟨fun n => (u n).1.1, fun n => (u n).1.2, fun n => (u n).2.1,
    fun n g => congrArg (fun p : S n => p.1.1 g) (hu n),
    fun n => congrArg (fun p : S n => p.1.2) (hu n), (u 1).2.2 Nat.one_pos⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem lift_seq {A : Type} [CommRing A] [IsLocalRing A] {T : Type} [AddCommGroup T] [Module A T]
    [IsPrecomplete (maximalIdeal A) T] (x : ∀ n, T ⧸ lev A T n) (hx : ∀ n, redn A T n (x (n + 1)) = x n) :
    ∃ L : T, ∀ n, (lev A T n).mkQ L = x n := by
  choose f hf using fun n => (lev A T n).mkQ_surjective (x n)
  have h1 : ∀ n, f n - f (n + 1) ∈ lev A T n := fun n => by
    rw [← Submodule.Quotient.eq]
    have := hx n
    rw [← hf (n + 1), redn_mk, ← hf n] at this
    exact this.symm
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ lev A T m := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h3 : lev A T n ≤ lev A T m := Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)
      simpa using (lev A T m).add_mem ih (h3 (h1 n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal A) f fun {m n} hmn => SModEq.sub_mem.2 (h2 m n hmn)
  exact ⟨L, fun n => Eq.trans (SModEq.def.1 (hL n).symm) (hf n)⟩

private theorem mem_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (P : Submodule A T) (x : T)
    (hx : ∀ n, (lev A T n).mkQ x ∈ P.map (lev A T n).mkQ) : x ∈ P := by
  rw [← Submodule.Quotient.mk_eq_zero]
  refine IsHausdorff.haus' (I := maximalIdeal A) _ fun n => ?_
  obtain ⟨p, hp, e⟩ := hx n
  have e' : p - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e
  have h1 : P.mkQ (p - x) ∈ (lev A T n).map P.mkQ := Submodule.mem_map_of_mem e'
  rw [Submodule.map_smul'', map_sub, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hp, zero_sub,
    neg_mem_iff] at h1
  rw [SModEq.zero]
  exact Submodule.smul_mono le_rfl le_top h1

private theorem eq_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (x y : T)
    (hx : ∀ n, (lev A T n).mkQ x = (lev A T n).mkQ y) : x = y := by
  rw [← sub_eq_zero, ← Submodule.mem_bot A]
  refine mem_of_lev ⊥ _ fun n => ?_
  rw [map_sub, hx n, sub_self]
  exact zero_mem _

theorem UpperTheory.V.Ws.Bl.limit :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), IsAdicComplete (maximalIdeal A) A → ∀ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) → (∀ n g, redn A T n (z (n + 1) g) = z n g) → (∀ n, redn A T n (y (n + 1)) = y n) → Prim (z 1) →
          ∃ (z' : Γ → T) (y' : T), IsZT ρ c N H P z' y' ∧ z' ≠ 0 := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hA z y hZ hz hy hP
  haveI : IsPrecomplete (maximalIdeal A) T := isPrecomplete_finite _
  choose z' hz' using fun g => lift_seq (fun n => z n g) fun n => hz n g
  obtain ⟨y', hy'⟩ := lift_seq y hy
  refine ⟨z', y', ⟨fun n => ?_, fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_⟩
  · simp only [hz']
    exact (hZ n).lc
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [map_add, ← modRep_mk, hz', hz', hz']
    exact (hZ n).coc g h
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).cz
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).kill g hg
  · refine mem_of_lev P _ fun n => ?_
    rw [map_sub, map_sub, ← modRep_mk, hz', hy']
    exact (hZ n).loc h hh
  · rintro rfl
    obtain ⟨g, hg⟩ := hP
    apply hg
    rw [← hz' g 1, Pi.zero_apply, map_zero]
    exact zero_mem _
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cocT :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (ρ : Representation A (G ℚ Ω) T) (P : Submodule A T) (K : Subgroup (G ℚ Ω)),
          IsAdicComplete (maximalIdeal A) A → (l : A) ∈ maximalIdeal A → Lat ρ (Dec (F := ℚ) B) P → (Function.Bijective fun x => ρ s x - x) → (∀ x, ρ c x = -x) → K ≤ ρ.ker → (∀ A', Raw.Away S A' → Ine (F := ℚ) A' ≤ K) →
          ∃ (z : G ℚ Ω → T) (y : T), IsZT ρ c (neSet l K) (Dec (F := ℚ) B) P z y ∧ z ≠ 0 := by
  intro hC Ω _ _ _ l _ S c s B hP A _ _ _ _ T _ _ _ _ ρ P K hA hl hL hs hc hK hU
  have hcard := cardP A T P hL.sat hL.ne
  have hfin : ∀ n, Finite (T ⧸ lev A T n) := fun n => (hcard n).1
  have htor : ∀ n, ∀ m : T ⧸ lev A T n, (l ^ n) • m = 0 := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul A, Nat.cast_pow]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl n) Submodule.mem_top
  have hlc : ∀ n, ∀ m : T ⧸ lev A T n, IsLocallyConstant fun g => modRep ρ n g m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    exact hL.cont n x
  have hker : ∀ n, K ≤ (modRep ρ n).ker := by
    intro n g hg
    have h1 : ρ g = 1 := hK hg
    refine LinearMap.ext fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, h1]
    rfl
  have hneg : ∀ n, ∀ m : T ⧸ lev A T n, modRep ρ n c m = -m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, hc, map_neg]
  have hbij : ∀ n, Function.Bijective fun m : T ⧸ lev A T n => modRep ρ n s m - m := by
    intro n
    haveI := hfin n
    refine Finite.surjective_iff_bijective.1 fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    obtain ⟨y, rfl⟩ := hs.2 x
    exact ⟨(lev A T n).mkQ y, by simp only [modRep_mk, map_sub]⟩
  have hstab : ∀ n, ∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P.map (lev A T n).mkQ, modRep ρ n h x ∈ P.map (lev A T n).mkQ := by
    rintro n h hh _ ⟨x, hx, rfl⟩
    exact ⟨ρ h x, hL.stab h hh x hx, rfl⟩
  have hZ : ∀ n, (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n).Finite := fun n => by
    haveI := hfin n
    exact zcFin hC.gf S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU _
  have hge : ∀ n, n ≤ Nat.card (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n) := fun n => by
    haveI := hfin n
    exact (hcard n).2.trans
      (gwCount hC S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU (hneg n) (hbij n) _ (hstab n))
  obtain ⟨z, y, h1, h2, h3, h4⟩ := compat A T _ ρ c _ _ P hfin hZ (primEx A T _ ρ c _ _ P hL hZ hge)
  exact limit A T _ ρ c _ _ P hA z y h1 h2 h3 h4
end
