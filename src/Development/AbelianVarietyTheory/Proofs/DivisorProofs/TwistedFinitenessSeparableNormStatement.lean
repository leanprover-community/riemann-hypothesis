import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFinitelyGeneratedModOpenStatement

section
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem frobR_mem_intR (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  intro x hx
  have hx' : ((x : PadicAlgCl p)) ∈ Obar p := hx
  show ((frobR p K r x : Kn p K r) : PadicAlgCl p) ∈ Obar p
  have h : ((frobR p K r x : Kn p K r) : PadicAlgCl p) = frobK p K (x : PadicAlgCl p) := rfl
  rw [h, mem_Obar_iff, norm_map_GK]
  exact mem_Obar_iff.1 hx'

end GlobalTheory.LKLoc
end

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_preserves_integer_ring : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  atlas_forward_decl GlobalTheory.LKLoc.frobR_mem_intR
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigKQ_mem_intKQ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    ∀ x ∈ intKQ p K r, sigKQ p K r x ∈ intKQ p K r := by
  have hle : intKQ p K r ≤ (intKQ p K r).comap (sigKQ p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · show sigKQ p K r (inclK p K r a) ∈ intKQ p K r
      have : sigKQ p K r (inclK p K r a) = inclK p K r a := by
        exact DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id ℚ_[p] K) (frobQ p r)) (a : K)
      rw [this]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · show sigKQ p K r (inclQ p K r b) ∈ intKQ p K r
      have hb : GlobalTheory.LKLoc.frobR p (Q0 p) r b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r :=
        GlobalTheory.T.frobenius_preserves_integer_ring p (Q0 p) r b b.2
      have : sigKQ p K r (inclQ p K r b) = inclQ p K r (⟨_, hb⟩ : GlobalTheory.LKLoc.intR p (Q0 p) r) := by
        simp [sigKQ, inclQ, Algebra.TensorProduct.map_tmul]
        rfl
      rw [this]
      exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  exact fun x hx => hle hx

theorem sigRes_mem_Kres : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ),
    ∀ g ∈ Kres p K n r, sigRes p K n r g ∈ Kres p K n r := by
  intro p _ K n r g hg
  obtain ⟨h, rfl⟩ := hg
  let f : intKQ p K r →+* intKQ p K r :=
    (sigKQ p K r).toRingHom.restrict (intKQ p K r) (intKQ p K r) (sigKQ_mem_intKQ p K r)
  refine ⟨GeneralLinearGroup.map f h, ?_⟩
  ext i j
  rfl

end GlobalTheory.LKRes
end

section
open scoped Classical

namespace GlobalTheory.LKMid.TwCent

open GlobalTheory.LKMid

variable {H : Type} [Group H] (θ : H →* H)

theorem nrmG_succ' (j : ℕ) (δ : H) : nrmG θ (j + 1) δ = nrmG θ j δ * (⇑θ)^[j] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem mul_map_nrmG (j : ℕ) (δ : H) : δ * θ (nrmG θ j δ) = nrmG θ (j + 1) δ := by
  induction j with
  | zero => simp [nrmG]
  | succ j ih =>
    rw [nrmG_succ' θ (j + 1), nrmG_succ', map_mul, ← mul_assoc, ih, ← Function.iterate_succ_apply' (⇑θ), nrmG_succ' θ j]

theorem iterate_twConj (δ : H) (i : ℕ) (h : H) :
    (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[i] h = nrmG θ i δ * (⇑θ)^[i] h * (nrmG θ i δ)⁻¹ := by
  induction i with
  | zero => simp [nrmG]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply' (⇑θ), ← mul_map_nrmG]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, mul_inv_rev, inv_inv]
    group

theorem main : ∀ {H : Type} [Group H] (θ : H →* H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, δ * θ z * δ⁻¹ ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) := by
  intro H _ θ δ r _ hθ
  have key : δ * θ (nrmG θ r δ) = nrmG θ r δ * δ := by
    rw [mul_map_nrmG, nrmG_succ', hθ]
  have hN : nrmG θ r δ = δ * θ (nrmG θ r δ) * δ⁻¹ := by rw [key]; group
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have h2 : θ (nrmG θ r δ) * θ z = θ z * θ (nrmG θ r δ) := by rw [← map_mul, ← hz, map_mul]
    symm
    calc nrmG θ r δ * (δ * θ z * δ⁻¹) = δ * (θ (nrmG θ r δ) * θ z) * δ⁻¹ := by
          conv_lhs => rw [hN]
          group
      _ = δ * (θ z * θ (nrmG θ r δ)) * δ⁻¹ := by rw [h2]
      _ = δ * θ z * δ⁻¹ * nrmG θ r δ := by
          conv_rhs => rw [hN]
          group
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz
    rw [iterate_twConj, hθ, ← hz, mul_inv_cancel_right]

end GlobalTheory.LKMid.TwCent
end

section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_norm_invariant : ∀ {H : Type} [Group H] (θ : H →* H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, δ * θ z * δ⁻¹ ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) := by
  first | (exact @GlobalTheory.LKMid.TwCent.main) | (exact GlobalTheory.LKMid.TwCent.main) | (intros; apply GlobalTheory.LKMid.TwCent.main  <;> assumption)
end

section
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwLangAb

theorem finite_nsmul_preimage {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (r : ℕ) (hr : 0 < r)
    (T : Set A) (hT : T.Finite) : {a : A | r • a ∈ T}.Finite := by
  let K : AddSubgroup A := (nsmulAddMonoidHom r : A →+ A).ker
  have h0 : Module.Finite ℤ (AddSubgroup.toIntSubmodule K) := inferInstance
  have h1 : Module.Finite ℤ K := h0
  have h2 : AddGroup.FG K := Module.Finite.iff_addGroup_fg.mp h1
  have hKf : Finite K := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun x => ?_
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨r, hr, ?_⟩
    apply Subtype.ext
    have hx : (nsmulAddMonoidHom r : A →+ A) (x : A) = 0 := AddMonoidHom.mem_ker.mp x.2
    simpa using hx
  have hKs : (K : Set A).Finite := Set.finite_coe_iff.mp hKf
  change ((fun a : A => r • a) ⁻¹' T).Finite
  refine hT.preimage' fun b _ => ?_
  by_cases hb : ∃ a0 : A, r • a0 = b
  · obtain ⟨a0, rfl⟩ := hb
    refine (hKs.image (fun k => a0 + k)).subset ?_
    intro a ha
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha
    refine ⟨a - a0, ?_, by simp⟩
    show a - a0 ∈ K
    simp [K, smul_sub, ha]
  · have : (fun a : A => r • a) ⁻¹' {b} = ∅ := by
      ext a; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hb ⟨a, h⟩
    rw [this]; exact Set.finite_empty

theorem finite_pow_preimage {Q : Type*} [CommGroup Q] [Group.FG Q] (r : ℕ) (hr : 0 < r)
    (T : Set Q) (hT : T.Finite) : {x : Q | x ^ r ∈ T}.Finite := by
  haveI : AddGroup.FG (Additive Q) := inferInstance
  haveI : Module.Finite ℤ (Additive Q) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h := finite_nsmul_preimage (A := Additive Q) r hr (Additive.toMul ⁻¹' T)
    (hT.preimage Additive.toMul.injective.injOn)
  refine (h.preimage (f := Additive.ofMul) Additive.ofMul.injective.injOn).subset ?_
  intro x hx
  simpa using hx

def fixedSubgroup {M : Type*} [Group M] (τ : M →* M) : Subgroup M where
  carrier := {x | τ x = x}
  one_mem' := map_one τ
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem iterate_eq_mul_prod {M : Type*} [CommGroup M] (τ : M →* M) (t : M) (i : ℕ) :
    (⇑τ)^[i] t = t * ∏ j ∈ Finset.range i, (⇑τ)^[j] (t⁻¹ * τ t) := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc (⇑τ)^[i + 1] t = (⇑τ)^[i] (τ t) := Function.iterate_succ_apply _ _ _
      _ = (⇑τ)^[i] (t * (t⁻¹ * τ t)) := by rw [mul_inv_cancel_left]
      _ = _ := by rw [iterate_map_mul, ih, Finset.prod_range_succ, mul_assoc]

theorem core {M : Type*} [CommGroup M] (τ : M →* M) (r : ℕ) (hr : 0 < r) (hτr : ∀ z, (⇑τ)^[r] z = z)
    (U : Subgroup M) (hU : ∀ u ∈ U, τ u ∈ U) (G : Set M) (hG : G.Finite)
    (hgen : ∀ z : M, z ∈ Subgroup.closure (G ∪ (U : Set M))) (F : Set M) (hF : F.Finite) :
    ∃ S : Finset M, ∀ t : M, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  let B := fixedSubgroup τ
  let K : Subgroup M := U ⊔ B
  let π : M →* M ⧸ K := QuotientGroup.mk' K
  have hUK : U ≤ K := le_sup_left
  have hBK : B ≤ K := le_sup_right
  haveI : Group.FG (M ⧸ K) := by
    refine Group.fg_iff.2 ⟨π '' G, ?_, hG.image _⟩
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective K q
    refine Subgroup.closure_induction (p := fun x _ => π x ∈ Subgroup.closure (π '' G)) ?_ ?_ ?_ ?_ (hgen z)
    · intro x hx
      rcases hx with hx | hx
      · exact Subgroup.subset_closure ⟨x, hx, rfl⟩
      · have : π x = 1 := (QuotientGroup.eq_one_iff x).2 (hUK hx)
        rw [this]; exact one_mem _
    · rw [map_one]; exact one_mem _
    · intro x y _ _ hx hy
      rw [map_mul]; exact mul_mem hx hy
    · intro x _ hx
      rw [map_inv]; exact inv_mem hx
  let P : M → M := fun c => ∏ i ∈ Finset.range r, ∏ j ∈ Finset.range i, (⇑τ)^[j] c
  have hPmul : ∀ a b, P (a * b) = P a * P b := by
    intro a b
    simp only [P, iterate_map_mul, Finset.prod_mul_distrib]
  have hit : ∀ j : ℕ, ∀ u ∈ U, (⇑τ)^[j] u ∈ U := by
    intro j
    induction j with
    | zero => intro u hu; exact hu
    | succ j ih => intro u hu; rw [Function.iterate_succ_apply']; exact hU _ (ih u hu)
  have hPU : ∀ u ∈ U, P u ∈ U := by
    intro u hu
    exact Subgroup.prod_mem _ fun i _ => Subgroup.prod_mem _ fun j _ => hit j u hu
  have key : ∀ t : M, π t ^ r = (π (P (t⁻¹ * τ t)))⁻¹ := by
    intro t
    let N := ∏ i ∈ Finset.range r, (⇑τ)^[i] t
    have hN : τ N = N := by
      have e1 : τ N = ∏ i ∈ Finset.range r, (⇑τ)^[i + 1] t := by
        simp only [N, map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Function.iterate_succ_apply']
      have e2 := Finset.prod_range_succ (fun i => (⇑τ)^[i] t) r
      have e3 := Finset.prod_range_succ' (fun i => (⇑τ)^[i] t) r
      rw [hτr t] at e2
      rw [Function.iterate_zero_apply] at e3
      rw [e1]
      have := e3.symm.trans e2
      exact mul_right_cancel this
    have hNe : N = t ^ r * P (t⁻¹ * τ t) := by
      simp only [N, P]
      rw [Finset.prod_congr rfl fun i _ => iterate_eq_mul_prod τ t i, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range]
    have hNK : π N = 1 := (QuotientGroup.eq_one_iff N).2 (hBK hN)
    rw [hNe, map_mul, map_pow] at hNK
    exact eq_inv_of_mul_eq_one_left hNK
  let T : Set (M ⧸ K) := (fun f => (π (P f))⁻¹) '' F
  have hX : {x : M ⧸ K | x ^ r ∈ T}.Finite := finite_pow_preimage r hr T (hF.image _)
  let σ := Function.surjInv (QuotientGroup.mk'_surjective K)
  refine ⟨hX.toFinset.image σ, ?_⟩
  rintro t ⟨f, hf, u, hu, hc⟩
  have hxT : π t ∈ {x : M ⧸ K | x ^ r ∈ T} := by
    show π t ^ r ∈ T
    refine ⟨f, hf, ?_⟩
    have h1 : π (P u) = 1 := (QuotientGroup.eq_one_iff _).2 (hUK (hPU u hu))
    show (π (P f))⁻¹ = π t ^ r
    rw [key t, hc, hPmul, map_mul, h1, mul_one]
  have hs : π (σ (π t)) = π t := Function.surjInv_eq _ _
  have hmem : (σ (π t))⁻¹ * t ∈ K := QuotientGroup.eq.mp hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
  refine ⟨z, hz, σ (π t), Finset.mem_image.2 ⟨π t, hX.mem_toFinset.2 hxT, rfl⟩, y, hy, ?_⟩
  have e : σ (π t) * (y * z) = t := by rw [hyz, mul_inv_cancel_left]
  calc t = σ (π t) * (y * z) := e.symm
    _ = z * σ (π t) * y := by ac_rfl

theorem exists_finite_reps_of_twisted_lang : ∀ {H : Type} [Group H] (Z U : Subgroup H) (τ : H →* H) (r : ℕ),
    0 < r → (∀ z ∈ Z, τ z ∈ Z) →
    (∀ z ∈ Z, (⇑τ)^[r] z = z) → (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → U ≤ Z → (∀ u ∈ U, τ u ∈ U) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) →
    ∀ F : Finset H, ∃ S : Finset H, ∀ t ∈ Z, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b ∈ Z, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  intro H _ Z U τ r hr hτZ hτr hcomm hUZ hU hGex F
  obtain ⟨G, hGZ, hcl⟩ := hGex
  letI : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let τ' : Z →* Z :=
    { toFun := fun z => ⟨τ z, hτZ z z.2⟩
      map_one' := Subtype.ext (map_one τ)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : H) (b : H)) }
  have hiter : ∀ (n : ℕ) (z : Z), (((⇑τ')^[n] z : Z) : H) = (⇑τ)^[n] (z : H) := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  let U' : Subgroup Z := U.subgroupOf Z
  let G' : Set Z := Subtype.val ⁻¹' (G : Set H)
  have hG' : G'.Finite := G.finite_toSet.preimage Subtype.val_injective.injOn
  have hle : Subgroup.closure ((G : Set H) ∪ (U : Set H)) ≤ Z :=
    (Subgroup.closure_le _).2 (Set.union_subset (fun g hg => hGZ g hg) hUZ)
  have hgen : ∀ z : Z, z ∈ Subgroup.closure (G' ∪ (U' : Set Z)) := by
    intro z
    have := Subgroup.closure_induction
      (p := fun x hx => (⟨x, hle hx⟩ : Z) ∈ Subgroup.closure (G' ∪ (U' : Set Z)))
      (fun x hx => by
        apply Subgroup.subset_closure
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Subgroup.mem_subgroupOf.2 hx))
      (one_mem _)
      (fun x y _ _ hx hy => mul_mem hx hy)
      (fun x _ hx => inv_mem hx) (hcl z.2)
    simpa using this
  let F' : Set Z := Subtype.val ⁻¹' (F : Set H)
  have hF' : F'.Finite := F.finite_toSet.preimage Subtype.val_injective.injOn
  obtain ⟨S', hS'⟩ := core τ' r hr (fun z => Subtype.ext (by rw [hiter]; exact hτr (z : H) z.2)) U'
    (fun u hu => Subgroup.mem_subgroupOf.2 (hU _ (Subgroup.mem_subgroupOf.1 hu))) G' hG' hgen F' hF'
  refine ⟨S'.image Subtype.val, ?_⟩
  rintro t ht ⟨f, hf, u, hu, hc⟩
  have hfe : f = t⁻¹ * τ t * u⁻¹ := by rw [hc, mul_inv_cancel_right]
  have hfZ : f ∈ Z := by
    rw [hfe]
    exact mul_mem (mul_mem (inv_mem ht) (hτZ t ht)) (inv_mem (hUZ hu))
  obtain ⟨b, hb, s, hs, u', hu', he⟩ := hS' ⟨t, ht⟩
    ⟨⟨f, hfZ⟩, hf, ⟨u, hUZ hu⟩, Subgroup.mem_subgroupOf.2 hu, Subtype.ext hc⟩
  exact ⟨b, b.2, congrArg Subtype.val hb, s, Finset.mem_image_of_mem _ hs, u',
    Subgroup.mem_subgroupOf.1 hu', congrArg Subtype.val he⟩

end GlobalTheory.TwLangAb
end
end

section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_fixed_coset_decomposition : ∀ {H : Type} [Group H] (Z U : Subgroup H) (τ : H →* H) (r : ℕ), 0 < r → (∀ z ∈ Z, τ z ∈ Z) →
    (∀ z ∈ Z, (⇑τ)^[r] z = z) → (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → U ≤ Z → (∀ u ∈ U, τ u ∈ U) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) →
    ∀ F : Finset H, ∃ S : Finset H, ∀ t ∈ Z, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b ∈ Z, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  first | (exact @GlobalTheory.TwLangAb.exists_finite_reps_of_twisted_lang) | (exact GlobalTheory.TwLangAb.exists_finite_reps_of_twisted_lang) | (intros; apply GlobalTheory.TwLangAb.exists_finite_reps_of_twisted_lang <;> assumption)
end

section
open scoped Classical

namespace GlobalTheory.TwistStab

variable {H : Type} [Group H]

theorem commensurable_comap {f : H →* H} (hf : Function.Surjective f) {A B : Subgroup H}
    (h : A.Commensurable B) : (A.comap f).Commensurable (B.comap f) :=
  ⟨by rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hf]; exact h.1,
   by rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hf]; exact h.2⟩

theorem finite_cover {A B : Subgroup H} (h : A.relIndex B ≠ 0) :
    ∃ R : Finset H, (∀ f ∈ R, f ∈ B) ∧ ∀ b ∈ B, ∃ f ∈ R, ∃ a ∈ A, b = f * a := by
  haveI : (A.subgroupOf B).FiniteIndex := ⟨h⟩
  haveI : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨(Set.finite_range (fun q : B ⧸ A.subgroupOf B => ((Quotient.out q : B) : H))).toFinset,
    ?_, ?_⟩
  · intro f hf
    simp only [Set.Finite.mem_toFinset, Set.mem_range] at hf
    obtain ⟨q, rfl⟩ := hf
    exact (Quotient.out q).2
  · intro b hb
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
    refine ⟨((Quotient.out (QuotientGroup.mk (⟨b, hb⟩ : B) : B ⧸ A.subgroupOf B) : B) : H), ?_,
      ((a : B) : H)⁻¹, ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨_, rfl⟩
    · exact A.inv_mem (Subgroup.mem_subgroupOf.mp a.2)
    · rw [ha]
      simp

def iterComap (T : H →* H) (K : Subgroup H) (n : ℕ) : Subgroup H :=
  (fun C : Subgroup H => C.comap T)^[n] K

theorem iterComap_succ (T : H →* H) (K : Subgroup H) (n : ℕ) :
    iterComap T K (n + 1) = (iterComap T K n).comap T :=
  Function.iterate_succ_apply' _ n K

theorem mem_iterComap (T : H →* H) (K : Subgroup H) :
    ∀ (n : ℕ) (x : H), x ∈ iterComap T K n ↔ (⇑T)^[n] x ∈ K
  | 0, _ => Iff.rfl
  | n + 1, x => by
    rw [iterComap_succ, Subgroup.mem_comap, mem_iterComap T K n, Function.iterate_succ_apply]

theorem stable_subgroup : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    ∀ Z : Subgroup H, (∀ z ∈ Z, δ * θ z * δ⁻¹ ∈ Z) → (∀ z ∈ Z, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ ((Z ⊓ K₀ : Subgroup H) : Set H))) →
    ∃ U : Subgroup H, U ≤ Z ∧ U ≤ K₀ ∧ (∀ u ∈ U, δ * θ u * δ⁻¹ ∈ U) ∧
      (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) ∧
      (∀ h g : H, ∃ F : Finset H, ∀ z ∈ Z, ∀ k ∈ K₀, z = h * k * g → ∃ f ∈ F, ∃ u ∈ U, z = f * u) := by
  intro H _ θ K₀ δ r hr hθr hθK hcomm Z hZ hZr hG
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  set T : H →* H := (MulAut.conj δ).toMonoidHom.comp θ with hT
  have hTapp : ∀ x, T x = δ * θ x * δ⁻¹ := fun x => by
    simp [T, MulAut.conj_apply]
  have hθs : Function.Surjective θ := fun y =>
    ⟨(⇑θ)^[s] y, by rw [← Function.iterate_succ_apply' (⇑θ) s y]; exact hθr y⟩
  have hTs : Function.Surjective T := fun y => by
    obtain ⟨x, hx⟩ := hθs (δ⁻¹ * y * δ)
    exact ⟨x, by rw [hTapp, hx]; group⟩
  have hθK' : ∀ n : ℕ, ∀ k ∈ K₀, (⇑θ)^[n] k ∈ K₀ := by
    intro n
    induction n with
    | zero => intro k hk; exact hk
    | succ n ih => intro k hk; rw [Function.iterate_succ_apply']; exact hθK _ (ih k hk)
  have hcθ : K₀.comap θ = K₀ := by
    ext x
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      have e : (⇑θ)^[s] (θ x) = x := by rw [← Function.iterate_succ_apply]; exact hθr x
      rw [← e]
      exact hθK' s _ hx
    · exact hθK x
  have hconj : K₀.comap (MulAut.conj δ).toMonoidHom = K₀.map (MulAut.conj δ⁻¹).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨δ * x * δ⁻¹, hx, by group⟩
    · rintro ⟨k, hk, rfl⟩
      convert hk using 1
      group
  have hTK : (K₀.comap T).Commensurable K₀ := by
    have h1 : (K₀.comap (MulAut.conj δ).toMonoidHom).Commensurable K₀ := hconj ▸ hcomm δ⁻¹
    have := commensurable_comap hθs h1
    rw [Subgroup.comap_comap, hcθ] at this
    exact this
  have hW : ∀ n, (iterComap T K₀ n).Commensurable K₀ := by
    intro n
    induction n with
    | zero => exact Subgroup.Commensurable.refl _
    | succ n ih => rw [iterComap_succ]; exact (commensurable_comap hTs ih).trans hTK
  set V : Subgroup H := ⨅ i : Fin (s + 1), iterComap T K₀ i with hV
  set U : Subgroup H := Z ⊓ V with hU
  have hfin : ∀ g : H, U.relIndex (Z ⊓ K₀.map (MulAut.conj g).toMonoidHom) ≠ 0 := by
    intro g
    apply Subgroup.relIndex_inf_ne_zero
    · rw [Subgroup.relIndex_eq_one.mpr inf_le_left]
      exact one_ne_zero
    · apply Subgroup.relIndex_iInf_ne_zero
      intro i
      exact Subgroup.relIndex_ne_zero_trans ((hW i).trans (hcomm g).symm).1
        (by rw [Subgroup.relIndex_eq_one.mpr inf_le_right]; exact one_ne_zero)
  have hUK : U ≤ K₀ := by
    intro u hu
    have := Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hu).2 ⟨0, Nat.succ_pos s⟩
    exact this
  refine ⟨U, inf_le_left, hUK, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨huZ, huV⟩ := Subgroup.mem_inf.mp hu
    rw [← hTapp]
    refine Subgroup.mem_inf.mpr ⟨by rw [hTapp]; exact hZ u huZ, ?_⟩
    rw [Subgroup.mem_iInf]
    intro i
    rw [mem_iterComap, ← Function.iterate_succ_apply]
    show (⇑T)^[(i : ℕ) + 1] u ∈ K₀
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (s + 1) with h | h
    · have := Subgroup.mem_iInf.mp huV ⟨(i : ℕ) + 1, h⟩
      rw [mem_iterComap] at this
      exact this
    · have e : (i : ℕ) + 1 = s + 1 := by omega
      rw [e, hZr u huZ]
      exact hUK hu
  · obtain ⟨R, hRB, hR⟩ := finite_cover (hfin 1)
    obtain ⟨G, hGZ, hGcl⟩ := hG
    refine ⟨G ∪ R, ?_, ?_⟩
    · intro g hg
      rcases Finset.mem_union.mp hg with h | h
      · exact hGZ g h
      · exact (Subgroup.mem_inf.mp (hRB g h)).1
    · refine hGcl.trans ((Subgroup.closure_le _).mpr ?_)
      rintro x (hx | hx)
      · exact Subgroup.subset_closure (Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left _ hx)))
      · have hx' := Subgroup.mem_inf.mp hx
        have hx1 : x ∈ Z ⊓ K₀.map (MulAut.conj (1 : H)).toMonoidHom :=
          Subgroup.mem_inf.mpr ⟨hx'.1, ⟨x, hx'.2, by simp [MulAut.conj_apply]⟩⟩
        obtain ⟨f, hf, a, ha, rfl⟩ := hR x hx1
        exact Subgroup.mul_mem _
          (Subgroup.subset_closure (Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right _ hf))))
          (Subgroup.subset_closure (Or.inr ha))
  · intro h g
    obtain ⟨R, -, hR⟩ := finite_cover (hfin g⁻¹)
    by_cases hex : ∃ z₀ ∈ Z, ∃ k₀ ∈ K₀, z₀ = h * k₀ * g
    · obtain ⟨z₀, hz₀, k₀, hk₀, rfl⟩ := hex
      refine ⟨R.image (fun f => h * k₀ * g * f), ?_⟩
      intro z hz k hk hzk
      have hmem : (h * k₀ * g)⁻¹ * z ∈ Z ⊓ K₀.map (MulAut.conj g⁻¹).toMonoidHom := by
        refine Subgroup.mem_inf.mpr ⟨Z.mul_mem (Z.inv_mem hz₀) hz,
          ⟨k₀⁻¹ * k, K₀.mul_mem (K₀.inv_mem hk₀) hk, ?_⟩⟩
        rw [hzk]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      obtain ⟨f, hf, a, ha, hfa⟩ := hR _ hmem
      refine ⟨h * k₀ * g * f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, a, ha, ?_⟩
      rw [mul_assoc (h * k₀ * g) f a, ← hfa]
      group
    · exact ⟨∅, fun z hz k hk hzk => absurd ⟨z, hz, k, hk, hzk⟩ hex⟩

end GlobalTheory.TwistStab
end

section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_norm_fixed_decomposition : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    ∀ Z : Subgroup H, (∀ z ∈ Z, δ * θ z * δ⁻¹ ∈ Z) → (∀ z ∈ Z, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ ((Z ⊓ K₀ : Subgroup H) : Set H))) →
    ∃ U : Subgroup H, U ≤ Z ∧ U ≤ K₀ ∧ (∀ u ∈ U, δ * θ u * δ⁻¹ ∈ U) ∧
      (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) ∧
      (∀ h g : H, ∃ F : Finset H, ∀ z ∈ Z, ∀ k ∈ K₀, z = h * k * g → ∃ f ∈ F, ∃ u ∈ U, z = f * u) := by
  first | (exact @GlobalTheory.TwistStab.stable_subgroup) | (exact GlobalTheory.TwistStab.stable_subgroup) | (intros; apply GlobalTheory.TwistStab.stable_subgroup  <;> assumption)
end

section
open Matrix Polynomial

namespace GlobalTheory.SemilocalConj

open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

theorem exists_isUnit_det_krylov {A : Type} [CommRing A] [Finite (MaximalSpectrum A)] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) A) (hs : g.charpoly.Separable) :
    ∃ v, IsUnit (krylov g v).det := by
  classical
  have hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

theorem exists_units_conj_of_charpoly_eq (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : ℕ)
    (M₀ M : Matrix (Fin n) (Fin n) A) (hs : M₀.charpoly.Separable) (hχ : M.charpoly = M₀.charpoly) :
    ∃ P : (Matrix (Fin n) (Fin n) A)ˣ, (P : Matrix (Fin n) (Fin n) A) * M₀ = M * P := by
  have hs' : M.charpoly.Separable := hχ ▸ hs
  obtain ⟨w, hw⟩ := exists_isUnit_det_krylov M₀ hs
  obtain ⟨v, hv⟩ := exists_isUnit_det_krylov M hs'
  obtain ⟨a, ha⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hw
  obtain ⟨b, hb⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv
  have h1 := GlobalTheory.Orb.mul_krylov_eq M₀ w
  have h2 := GlobalTheory.Orb.mul_krylov_eq M v
  rw [← ha] at h1
  rw [← hb, hχ] at h2
  have h3 : ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) * M₀ =
      GlobalTheory.Orb.companionMat n M₀.charpoly * ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) := by
    calc ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) * M₀
        = (↑a⁻¹ * M₀ * ↑a) * ↑a⁻¹ := by rw [mul_assoc _ (a : Matrix (Fin n) (Fin n) A), Units.mul_inv, mul_one]
      _ = ↑a⁻¹ * (↑a * GlobalTheory.Orb.companionMat n M₀.charpoly) * ↑a⁻¹ := by rw [mul_assoc (↑a⁻¹) M₀, h1]
      _ = GlobalTheory.Orb.companionMat n M₀.charpoly * ↑a⁻¹ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨b * a⁻¹, ?_⟩
  rw [Units.val_mul, ← mul_assoc, h2, mul_assoc, h3, mul_assoc]

example : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : ℕ) (M₀ M : Matrix (Fin n) (Fin n) A),
    M₀.charpoly.Separable → M.charpoly = M₀.charpoly →
      ∃ P : (Matrix (Fin n) (Fin n) A)ˣ, (P : Matrix (Fin n) (Fin n) A) * M₀ = M * P :=
  exists_units_conj_of_charpoly_eq

end GlobalTheory.SemilocalConj
end

section
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes.CentComm

theorem commute_of_commute_of_separable {A : Type} [CommRing A] [Finite (MaximalSpectrum A)] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) A) (hs : g.charpoly.Separable) (X Y : Matrix (Fin n) (Fin n) A)
    (hX : Commute X g) (hY : Commute Y g) : X * Y = Y * X := by
  obtain ⟨v, hv⟩ := GlobalTheory.SemilocalConj.exists_isUnit_det_krylov g hs
  obtain ⟨q, rfl⟩ := GlobalTheory.BCT.FinCentComm.eq_aeval_of_cyclic g v hv Y hY
  exact (GlobalTheory.BCT.FinCentComm.commute_aeval hX q).eq

theorem finite_maximalSpectrum_KQ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (r : ℕ) (hr : 0 < r) : Finite (MaximalSpectrum (KQ p K r)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : Module.Finite ℚ_[p] (KQ p K r) := inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsArtinianRing (KQ p K r) := IsArtinianRing.of_finite ℚ_[p] (KQ p K r)
  infer_instance

theorem centralizer_comm : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∀ a ∈ Subgroup.centralizer {N}, ∀ b ∈ Subgroup.centralizer {N}, a * b = b * a := by
  intro p _ K hK n r hr N hs a ha b hb
  haveI := hK
  haveI := finite_maximalSpectrum_KQ p K r hr
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hX : Commute a.val N.val := by
    show a.val * N.val = N.val * a.val
    have := congrArg Units.val ha; simpa using this
  have hY : Commute b.val N.val := by
    show b.val * N.val = N.val * b.val
    have := congrArg Units.val hb; simpa using this
  exact Units.ext (by simpa using commute_of_commute_of_separable N.val hs a.val b.val hX hY)

end GlobalTheory.LKRes.CentComm

example : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∀ a ∈ Subgroup.centralizer {N}, ∀ b ∈ Subgroup.centralizer {N}, a * b = b * a :=
  GlobalTheory.LKRes.CentComm.centralizer_comm
end

section
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_centralizer_commutative : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∀ a ∈ Subgroup.centralizer {N}, ∀ b ∈ Subgroup.centralizer {N}, a * b = b * a := by
  first | (exact @GlobalTheory.LKRes.CentComm.centralizer_comm) | (exact GlobalTheory.LKRes.CentComm.centralizer_comm) | (intros; apply GlobalTheory.LKRes.CentComm.centralizer_comm  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFinGL

theorem twFin_generic : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    (∀ a ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, ∀ b ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, a * b = b * a) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
      Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} ≤
        Subgroup.closure ((G : Set H) ∪ ((Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} ⊓ K₀ : Subgroup H) : Set H))) →
    GlobalTheory.TwFin.TwFin θ K₀ δ (GlobalTheory.LKMid.nrmG θ r δ) := by
  intro H _ θ K₀ δ r hr hθr hθK hcomm hZc hfg
  obtain ⟨hτZ, hτr⟩ := GlobalTheory.T.twisted_centralizer_norm_invariant θ δ r hr hθr
  obtain ⟨U, hUZ, hUK, hUτ, hUfg, hUcov⟩ :=
    GlobalTheory.T.twisted_norm_fixed_decomposition θ K₀ δ r hr hθr hθK hcomm _ hτZ hτr hfg
  intro E
  choose! F hF using hUcov
  obtain ⟨S, hS⟩ := GlobalTheory.T.twisted_fixed_coset_decomposition _ U ((MulAut.conj δ).toMonoidHom.comp θ) r hr hτZ hτr hZc hUZ hUτ hUfg
    (E.biUnion fun e => F e δ⁻¹)
  refine ⟨S, ?_⟩
  intro t htN hE
  obtain ⟨e, he, k, hk, hek⟩ := hE
  have htZ : t ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]; exact htN.symm
  have hτt : ((MulAut.conj δ).toMonoidHom.comp θ) t = δ * θ t * δ⁻¹ := rfl
  have hc : t⁻¹ * ((MulAut.conj δ).toMonoidHom.comp θ) t ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ htZ) (hτZ t htZ)
  have hc' : t⁻¹ * ((MulAut.conj δ).toMonoidHom.comp θ) t = e * k * δ⁻¹ := by
    rw [hτt, ← mul_assoc, ← mul_assoc, hek]
  obtain ⟨f, hf, u, hu, hfu⟩ := hF e δ⁻¹ _ hc k hk hc'
  obtain ⟨b, -, hbτ, s, hs, u', hu', hbt⟩ :=
    hS t htZ ⟨f, Finset.mem_biUnion.2 ⟨e, he, hf⟩, u, hu, hfu⟩
  refine ⟨b, ?_, s, hs, u', hUK hu', hbt⟩
  change b * δ = δ * θ b
  have h1 : δ * θ b * δ⁻¹ = b := hbτ
  calc b * δ = δ * θ b * δ⁻¹ * δ := by rw [h1]
    _ = δ * θ b := by rw [inv_mul_cancel_right]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ δ : GL (Fin n) (KQ p K r), (nrmRes p K n r δ).val.charpoly.Separable → GlobalTheory.TwFin.TwFin (sigRes p K n r) (Kres p K n r) δ (nrmRes p K n r δ) := by
  intro p _ K hK n r hr δ hsep
  haveI := hK
  exact twFin_generic (sigRes p K n r) (Kres p K n r) δ r hr (sigRes_iterate_eq_self p K n r hr)
    (sigRes_mem_Kres p K n r) (fun g => GlobalTheory.HeckeP.Kres_commensurable p K n r hr g)
    (GlobalTheory.T.separable_centralizer_commutative p K hK n r hr _ hsep) (GlobalTheory.T.centralizer_finitely_generated_mod_open p K hK n r hr _ hsep)

end GlobalTheory.TwFinGL
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_finiteness_separable_norm : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ δ : GL (Fin n) (KQ p K r), (nrmRes p K n r δ).val.charpoly.Separable → GlobalTheory.TwFin.TwFin (sigRes p K n r) (Kres p K n r) δ (nrmRes p K n r δ) := by
  first | (exact @GlobalTheory.TwFinGL.main) | (exact GlobalTheory.TwFinGL.main) | (intros; apply GlobalTheory.TwFinGL.main <;> assumption)
end
