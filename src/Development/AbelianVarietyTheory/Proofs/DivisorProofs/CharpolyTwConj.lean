import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSphericalUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassCountCharPoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
import BuildAid.ForwardExisting

section
section
open Filter
open scoped Classical

namespace GlobalTheory.LocalGrouping

open Function

theorem ne_zero_of_finprod_mem_ne_zero {ι : Type} (S : Set ι) (h : ι → ℂ)
    (hf : (mulSupport h).Finite) (hne : ∏ᶠ i ∈ S, h i ≠ 0) : ∀ i ∈ S, h i ≠ 0 := by
  intro i hi hzero
  apply hne
  have hfin : (S ∩ mulSupport h).Finite := hf.subset Set.inter_subset_right
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
  apply Finset.prod_eq_zero (i := i)
  · simp [Set.Finite.mem_toFinset, hi, Function.mem_mulSupport, hzero]
  · exact hzero

theorem finprod_finsum_eq (I : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0) :
    ∏ᶠ i ∈ S, ∑ᶠ d, B i d = ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by
  have hone : ∀ i ∈ S, i ∉ T → ∑ᶠ d, B i d = 1 := by
    intro i hi hT
    rw [finsum_eq_single _ (u i)]
    · simp [hind i hi hT]
    · intro d hd; simp [hind i hi hT, hd]
  rw [finprod_mem_eq_prod_of_subset _ (t := T) ?_ hTS]
  swap
  · rintro i ⟨hiS, hi⟩
    by_contra hT
    exact hi (hone i hiS hT)
  let P : ∀ i : T, Finset (D i) := fun i => (hfin i (hTS i.2)).toFinset
  have hsum : ∀ i : T, ∑ᶠ d, B i d = ∑ d ∈ P i, B i d := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp [P])
  rw [← Finset.prod_coe_sort T, Finset.prod_congr rfl (fun i _ => hsum i), Finset.prod_univ_sum]
  symm
  apply finsum_eq_sum_of_support_subset
  intro f hf
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hf
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  simpa [P] using hf i (Finset.mem_univ _)

end GlobalTheory.LocalGrouping

namespace GlobalTheory.LocalGrouping

open Function

theorem finsum_fibres_eq (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0)
    (H3 : ∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1)
    (H4 : ∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
      Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) :
    (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
      (2 : ℂ) ^ m * ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by
  let F : (∀ i : T, D i) → ℂ := fun f => ∏ i : T, B i (f i)
  have hFfin : (support F).Finite := by
    apply (Set.Finite.pi (t := fun i : T => support (B i)) (fun i => hfin i (hTS i.2))).subset
    intro f hf
    rw [mem_support, Finset.prod_ne_zero_iff] at hf
    intro i _
    exact hf i (Finset.mem_univ _)
  let E : (∀ i : T, D i) → ∀ i, D i := fun f i => if h : i ∈ T then f ⟨i, h⟩ else u i
  let Fib : (∀ i : T, D i) → Set R := fun f => {c | c ∈ A ∧ ∀ i ∈ S, ℓ c i = E f i}
  have hEnz : ∀ f, F f ≠ 0 → ∀ i ∈ S, B i (E f i) ≠ 0 := by
    intro f hf i hi
    by_cases hT : i ∈ T
    · simp only [E, hT, dite_true]
      rw [Finset.prod_ne_zero_iff] at hf
      exact hf ⟨i, hT⟩ (Finset.mem_univ _)
    · simp [E, hT, hind i hi hT]
  have hcard : ∀ f, F f ≠ 0 → (Nat.card (Fib f) : ℂ) * 2 ^ k = 2 ^ m := by
    intro f hf
    have h := H4 (E f) (hEnz f hf)
    exact_mod_cast h
  have hFibfin : ∀ f, F f ≠ 0 → (Fib f).Finite := by
    intro f hf
    have h := H4 (E f) (hEnz f hf)
    have hne : Nat.card (Fib f) ≠ 0 := by
      intro h0
      change Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = E f i} = 0 at h0
      rw [h0, zero_mul] at h
      exact (pow_ne_zero m two_ne_zero) h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  have hpt : ∀ c, (if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) =
      ∑ f ∈ hFfin.toFinset, if c ∈ Fib f then F f else 0 := by
    intro c
    by_cases hcA : c ∈ A
    swap
    · simp [hcA, Fib]
    rw [if_pos hcA]
    by_cases hex : ∃ f ∈ hFfin.toFinset, c ∈ Fib f
    · obtain ⟨f, hf, hcf⟩ := hex
      rw [Finset.sum_eq_single f]
      · rw [if_pos hcf]
        rw [finprod_mem_eq_prod_of_subset _ (t := T) ?_ hTS]
        · rw [← Finset.prod_coe_sort T]
          apply Finset.prod_congr rfl
          intro i _
          rw [hcf.2 i (hTS i.2)]
          simp [E]
        · rintro i ⟨hiS, hi⟩
          by_contra hT
          apply hi
          show B i (ℓ c i) = 1
          have hT' : i ∉ T := hT
          rw [hcf.2 i hiS]
          simp [E, hT', hind i hiS hT']
      · intro g _ hgf
        rw [if_neg]
        intro hcg
        apply hgf
        funext i
        have h1 := hcf.2 i (hTS i.2)
        have h2 := hcg.2 i (hTS i.2)
        simp [E] at h1 h2
        rw [← h1, ← h2]
      · intro hf'; exact absurd hf hf'
    · rw [Finset.sum_eq_zero]
      swap
      · intro f hf
        rw [if_neg]
        intro hcf; exact hex ⟨f, hf, hcf⟩
      by_contra hne
      have hmf : (mulSupport fun i => B i (ℓ c i)).Finite := Filter.eventually_cofinite.mp (H3 c hcA)
      have hall := ne_zero_of_finprod_mem_ne_zero S _ hmf hne
      apply hex
      refine ⟨fun i => ℓ c i, ?_, hcA, ?_⟩
      · rw [Set.Finite.mem_toFinset, mem_support, Finset.prod_ne_zero_iff]
        intro i _
        exact hall i (hTS i.2)
      · intro i hi
        by_cases hT : i ∈ T
        · simp [E, hT]
        · have := hall i hi
          rw [hind i hi hT] at this
          simp only [E, hT, dite_false]
          by_contra h; exact this (if_neg h)
  have hinner : ∀ f ∈ hFfin.toFinset,
      (∑ᶠ c, if c ∈ Fib f then F f else 0) * (2 : ℂ) ^ k = 2 ^ m * F f := by
    intro f hf
    rw [Set.Finite.mem_toFinset, mem_support] at hf
    have e1 : (∑ᶠ c, if c ∈ Fib f then F f else 0) = ∑ᶠ c ∈ Fib f, F f := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro c
      simp [Set.indicator_apply]
    rw [e1, finsum_mem_eq_finite_toFinset_sum _ (hFibfin f hf), Finset.sum_const,
      ← Nat.card_eq_card_finite_toFinset, nsmul_eq_mul, mul_right_comm, hcard f hf]
  rw [finsum_congr hpt, finsum_sum_comm, Finset.sum_mul, Finset.sum_congr rfl hinner,
    ← Finset.mul_sum]
  · congr 1
    symm
    exact finsum_eq_sum_of_support_subset F (by simp)
  · intro f hf
    rw [Set.Finite.mem_toFinset, mem_support] at hf
    apply (hFibfin f hf).subset
    intro c hc
    by_contra h
    exact hc (if_neg h)

end GlobalTheory.LocalGrouping

namespace GlobalTheory

open Function

theorem finsum_finprod_mul_two_pow_eq :
    ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R)
      (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) →
      (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) →
      (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) →
      (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
        Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) →
      (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
        (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  intro I R D S B ℓ A k m H0 H1 H2 H3 H4
  have hbad : {i | ¬ ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0}.Finite :=
    Filter.eventually_cofinite.mp H2
  let T : Finset I := (hbad.inter_of_left S).toFinset
  let u : ∀ i, D i := fun i =>
    if h : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 then h.choose else (H0 i).some
  have hTS : (T : Set I) ⊆ S := by
    intro i hi
    simp only [T, Set.Finite.coe_toFinset] at hi
    exact hi.2
  have hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0 := by
    intro i hi hT
    have hgood : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 := by
      by_contra h
      apply hT
      rw [Set.Finite.mem_toFinset]
      exact ⟨h, hi⟩
    intro d
    simp only [u, hgood, dite_true]
    exact hgood.choose_spec d
  rw [LocalGrouping.finprod_finsum_eq I D S B T u hTS H1 hind]
  exact LocalGrouping.finsum_fibres_eq I R D S B ℓ A k m T u hTS H1 hind H3 H4

end GlobalTheory
end

open Filter
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_restricted_product_count : ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) → (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) → (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) → (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) → Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) → (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k = (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  atlas_forward_decl GlobalTheory.finsum_finprod_mul_two_pow_eq
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FibStable

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun x => ⟨1, by simp⟩, fun ⟨g, h⟩ => ⟨g⁻¹, by rw [h, map_inv]; group⟩,
    fun ⟨g, h⟩ ⟨k, h'⟩ => ⟨g * k, by rw [h', h, map_mul]; group⟩⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

theorem rep_cls (θ : G →* G) (y : G) : ∃ g, (cls θ y).rep = g⁻¹ * y * θ g :=
  (cls_eq_iff θ _ _).1 (cls_rep θ (cls θ y)).symm

theorem index_ne_zero [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsLevel θ K K') (f : G → ℂ) (hf : IsHecke K' f) (δ x : G) :
    (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  obtain ⟨ho, -, hθ⟩ := hK'
  have h1 : K'.subgroupOf K ≤ rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)) := by
    intro k' hk' k
    rw [Subgroup.mem_subgroupOf] at hk'
    have e : (x * ((k * k' : K) : G))⁻¹ * δ * θ (x * ((k * k' : K) : G)) =
        (k' : G)⁻¹ * ((x * k)⁻¹ * δ * θ (x * k)) * θ k' := by
      simp only [Subgroup.coe_mul, map_mul]; group
    show f _ = f _
    rw [e, (hf.2 _ (hθ _ hk') _).2, (hf.2 _ (K'.inv_mem hk') _).1]
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ho' : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := ho.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho'
  have h2 : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h0
  exact h2 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le h1))

theorem eq_single {D : Type} (B : D → ℂ) (h01 : ∀ d, B d = 0 ∨ B d = 1) (hs : ∑ᶠ d, B d = 1) :
    ∃ u, ∀ d, B d = if d = u then 1 else 0 := by
  have hfin : (Function.support B).Finite := by
    by_contra h
    rw [finsum_of_infinite_support h] at hs
    exact zero_ne_one hs
  rw [finsum_eq_sum _ hfin] at hs
  have hc : hfin.toFinset.card = 1 := by
    have : ∑ d ∈ hfin.toFinset, B d = (hfin.toFinset.card : ℂ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rcases h01 d with h | h
      · exact absurd h hd
      · simp [h]
    rw [this] at hs
    exact_mod_cast hs
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc
  refine ⟨u, fun d => ?_⟩
  split_ifs with h
  · subst h
    have : d ∈ hfin.toFinset := by rw [hu]; exact Finset.mem_singleton_self _
    rw [Set.Finite.mem_toFinset] at this
    rcases h01 d with h' | h'
    · exact absurd h' this
    · exact h'
  · by_contra hne
    have : d ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hne
    rw [hu, Finset.mem_singleton] at this
    exact h this

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def locTerm (n : ℕ) (w : Pl E) (P : E[X]) (φ : GLw n w → ℂ) (d : TwCl (thL n w)) : ℂ :=
  if (nrmL n w d.rep).val.charpoly = atPl w P then twOrb (thL n w) (GlobalTheory.LFun.KGL w n) d.rep φ else 0

theorem charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [nrmL_twConj, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

theorem stTw_eq (n : ℕ) (w : Pl E) (P : E[X]) (φ : GLw n w → ℂ) :
    stTw n w (atPl w P) φ = ∑ᶠ d, locTerm n w P φ d := by
  unfold stTw clSum locTerm
  refine finsum_congr fun d => ?_
  simp only [Set.mem_setOf_eq, Pi.one_apply, one_mul]

theorem locTerm_cls (n : ℕ) (w : Pl E) (P : E[X]) (K' : Subgroup (GLw n w))
    (hK' : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K') (φ : GLw n w → ℂ) (hφ : IsHecke K' φ) (y : GLw n w)
    (hy : (nrmL n w y).val.charpoly = atPl w P) :
    locTerm n w P φ (cls (thL n w) y) = twOrb (thL n w) (GlobalTheory.LFun.KGL w n) y φ := by
  obtain ⟨g, hg⟩ := rep_cls (thL n w) y
  unfold locTerm
  rw [hg, charpoly_twConj, if_pos hy]
  apply GlobalTheory.TwOrbConj.twOrb_twConj
  intro x
  exact index_ne_zero _ _ _ (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2 hK' φ hφ y x

end Local

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (GLw n w), IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' → ∀ φ : ∀ w : Pl E, GLw n w → ℂ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → ∀ P ∈ Ell E n, (∑ᶠ c : TwCl (thE E n), if (c.rep * thE E n c.rep).val.charpoly = P then ∏ᶠ w ∈ S, twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (locEl n w c.rep) (φ w) else 0) * (2 : ℂ) ^ nfac P = (2 : ℂ) ^ (n * Fintype.card (InfinitePlace E)) * ∏ᶠ w ∈ S, stTw n w (atPl w P) (φ w) := by
  intro E _ _ _ hU n S hS K' hK' φ hφ P hP
  obtain ⟨δ₀, hδ₀⟩ := (GlobalTheory.T.kappaConstant_mul_of_coprime_ellipticPolynomials E hU n 0 P 1 hP
    ⟨monic_one, natDegree_one, separable_one, fun τ z hz => by simp at hz⟩ isCoprime_one_right).2.1
  obtain ⟨A, hA⟩ : ∃ A : Set (TwCl (thE E n)), A = {c | (c.rep * thE E n c.rep).val.charpoly = P} := ⟨_, rfl⟩
  have hcA : ∀ c, c ∈ A ↔ (c.rep * thE E n c.rep).val.charpoly = P := fun c => by rw [hA]; rfl
  have hL : (∑ᶠ c : TwCl (thE E n), if (c.rep * thE E n c.rep).val.charpoly = P then
      ∏ᶠ w ∈ S, twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (locEl n w c.rep) (φ w) else 0) =
      ∑ᶠ c : TwCl (thE E n), if c ∈ A then
      ∏ᶠ w ∈ S, locTerm n w P (φ w) (cls (thL n w) (locEl n w c.rep)) else 0 := by
    refine finsum_congr fun c => ?_
    by_cases hc : (c.rep * thE E n c.rep).val.charpoly = P
    · rw [if_pos hc, if_pos ((hcA c).2 hc)]
      exact finprod_mem_congr rfl fun w _ => (locTerm_cls n w P (K' w) (hK'.1 w) (φ w) (hφ.1 w) _
        (by rw [ThBasic.charpoly_nrmL hU, hc])).symm
    · rw [if_neg hc, if_neg (fun h => hc ((hcA c).1 h))]
  have hR : ∏ᶠ w ∈ S, stTw n w (atPl w P) (φ w) = ∏ᶠ w ∈ S, ∑ᶠ d, locTerm n w P (φ w) d :=
    finprod_mem_congr rfl fun w _ => stTw_eq n w P (φ w)
  rw [hL, hR]
  refine GlobalTheory.T.finsum_restricted_product_count (Pl E) (TwCl (thE E n)) (fun w => TwCl (thL n w)) S (fun w => locTerm n w P (φ w))
    (fun c w => cls (thL n w) (locEl n w c.rep)) A
    (nfac P) (n * Fintype.card (InfinitePlace E)) (fun w => ⟨cls _ 1⟩) ?_ ?_ ?_ ?_
  · intro w _
    refine (GlobalTheory.BCT.ClsFin.classes_finite E hU n w (atPl w P) hP.2.2.1.map).1.subset fun d hd => ?_
    by_contra h
    exact Function.mem_support.1 hd (by unfold locTerm; exact if_neg h)
  · filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GlobalTheory.T.stable_twisted_orbital_unit_almost_all E hU n P hP] with w h1 h2 h3
    refine eq_single _ (fun d => ?_) ?_
    · try dsimp only
      unfold locTerm
      rw [h2]
      split_ifs with h
      · rw [h1 _ h]; split_ifs <;> simp
      · exact Or.inl rfl
    · try dsimp only
      rw [← stTw_eq, h2]
      exact h3
  · intro c hc
    rw [hcA] at hc
    filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GoodInt.eventually_mem_KGL c.rep,
      GoodInt.eventually_mem_KGL (c.rep * thE E n c.rep)] with w h1 h2 h3 h4
    have hy : (nrmL n w (locEl n w c.rep)).val.charpoly = atPl w P := by rw [ThBasic.charpoly_nrmL hU, hc]
    have hK : locEl n w c.rep ∈ GlobalTheory.LFun.KGL w n := by
      unfold locEl
      split_ifs
      exacts [h4, h3]
    try dsimp only
    rw [locTerm_cls n w P (K' w) (hK'.1 w) (φ w) (hφ.1 w) _ hy, h2, h1 _ hy, if_pos ⟨1, by simpa using hK⟩]
  · intro e he
    try dsimp only at he
    have hpoly : ∀ w ∈ S, (nrmL n w (e w).rep).val.charpoly = atPl w P := fun w hw => by
      by_contra h
      exact he w hw (by unfold locTerm; exact if_neg h)
    obtain ⟨y, hyS, hy1, hy2⟩ : ∃ y : ∀ w, GLw n w, (∀ w ∈ S, cls (thL n w) (y w) = e w) ∧
        (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) ∧ ∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n := by
      refine ⟨fun w => if w ∈ S then (if h : ∃ g : GLw n w, g⁻¹ * (e w).rep * thL n w g ∈ GlobalTheory.LFun.KGL w n then
          h.choose⁻¹ * (e w).rep * thL n w h.choose else (e w).rep) else locEl n w δ₀, fun w hw => ?_, fun w => ?_, ?_⟩
      · try dsimp only
        rw [if_pos hw]
        split_ifs with h
        · rw [← (cls_eq_iff (thL n w) (e w).rep _).2 ⟨h.choose, rfl⟩, cls_rep]
        · exact cls_rep _ _
      · try dsimp only
        split_ifs with hw h
        · rw [charpoly_twConj]; exact hpoly w hw
        · exact hpoly w hw
        · rw [ThBasic.charpoly_nrmL hU, hδ₀]
      · filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GoodInt.eventually_mem_KGL δ₀,
          GoodInt.eventually_mem_KGL (δ₀ * thE E n δ₀)] with w h1 h2 h3 h4
        try dsimp only
        split_ifs with hw h
        · exact h.choose_spec
        · exfalso
          have hne := he w hw
          unfold locTerm at hne
          rw [if_pos (hpoly w hw), h2, h1 _ (hpoly w hw), if_neg h] at hne
          exact hne rfl
        · unfold locEl
          split_ifs
          exacts [h4, h3]
    have hc := GlobalTheory.T.twisted_class_count_char_poly E hU n S hS P hP y hy1 hy2
    convert hc using 2
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => and_congr (hcA c) (forall₂_congr fun w hw => ?_))
    try dsimp only
    rw [← hyS w hw, eq_comm, cls_eq_iff]

end GlobalTheory.BCT.FibStable
end
end
