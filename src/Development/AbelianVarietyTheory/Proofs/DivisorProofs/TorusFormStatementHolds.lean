import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrdering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalAppellHumbertRealMult
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledUniformization

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_embedding_ordering : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := by
  first | exact @GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings | exact GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings | (intros; apply GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem realEmb_linearIndependent_on_integers (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ) :
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := by
  intro h
  have hall : ∀ x : F, ∑ τ, a τ * τ x = 0 := by
    intro x
    have halg : IsAlgebraic ℤ x := by
      first
        | exact Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x
        | (haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
           exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).isAlgebraic.restrictScalars ℤ)
    obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
    have h1 : ∑ τ : F →+* ℝ, a τ * τ (y • x) = 0 := h ⟨y • x, hint⟩
    rw [zsmul_eq_mul] at h1
    have h2 : ∑ τ : F →+* ℝ, a τ * τ ((y : F) * x) = (y : ℝ) * ∑ τ, a τ * τ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, map_intCast]; ring
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h4 | h4
    · exact absurd (by exact_mod_cast h4) hy
    · exact h4
  have hli : LinearIndependent ℝ (fun τ : F →+* ℝ => ((τ : F →* ℝ) : F → ℝ)) :=
    (linearIndependent_monoidHom F ℝ).comp (fun τ : F →+* ℝ => (τ : F →* ℝ))
      (fun τ σ hτσ => RingHom.ext fun x => DFunLike.congr_fun hτσ x)
  funext τ
  refine Fintype.linearIndependent_iff.mp hli a ?_ τ
  funext x
  simpa [Finset.sum_apply, smul_eq_mul] using hall x

example : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := fun F _ _ a h => GlobalTheory.realEmb_linearIndependent_on_integers F a h

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_embeddings_linearly_independent : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := by
  atlas_forward_decl GlobalTheory.realEmb_linearIndependent_on_integers
end

section
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem alternating_pairing_expand {F V : Type} [Field F] [NumberField F] [AddCommGroup V]
    [Module F V] (L : Set V)
    (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hsm : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (Q : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, Q x x' = -Q x' x)
    (hQadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, Q (x₁ + x₂) x' = Q x₁ x' + Q x₂ x')
    (hQsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, Q ((a : F) • x) x' = (a : F) * Q x x')
    {x x' : V} (hx : x ∈ L) (hx' : x' ∈ L) (r₀ r₁ s₀ s₁ : 𝓞 F) :
    Q ((r₀ : F) • x + (r₁ : F) • x') ((s₀ : F) • x + (s₁ : F) • x') =
      ((r₀ : F) * s₁ - (r₁ : F) * s₀) * Q x x' := by
  have hself : ∀ y ∈ L, Q y y = 0 := by
    intro y hy
    have h := halt y hy y hy
    have h2 : (2 : F) * Q y y = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hadd2 : ∀ y ∈ L, ∀ y₁ ∈ L, ∀ y₂ ∈ L, Q y (y₁ + y₂) = Q y y₁ + Q y y₂ := by
    intro y hy y₁ hy₁ y₂ hy₂
    have e1 := halt y hy _ (hadd _ hy₁ _ hy₂)
    have e2 := hQadd _ hy₁ _ hy₂ _ hy
    have e3 := halt y hy y₁ hy₁
    have e4 := halt y hy y₂ hy₂
    linear_combination e1 - e2 - e3 - e4
  have hsmul2 : ∀ y ∈ L, ∀ (a : 𝓞 F), ∀ y' ∈ L, Q y ((a : F) • y') = (a : F) * Q y y' := by
    intro y hy a y' hy'
    have e1 := halt y hy _ (hsm a y' hy')
    have e2 := hQsmul a y' hy' y hy
    have e3 := halt y hy y' hy'
    linear_combination e1 - e2 - (a : F) * e3
  have hu := hsm r₀ x hx
  have hv := hsm r₁ x' hx'
  have hp := hsm s₀ x hx
  have hq := hsm s₁ x' hx'
  rw [hQadd _ hu _ hv _ (hadd _ hp _ hq), hadd2 _ hu _ hp _ hq, hadd2 _ hv _ hp _ hq,
    hQsmul r₀ x hx _ hp, hQsmul r₀ x hx _ hq, hQsmul r₁ x' hx' _ hp, hQsmul r₁ x' hx' _ hq,
    hsmul2 x hx s₀ x hx, hsmul2 x hx s₁ x' hx', hsmul2 x' hx' s₀ x hx, hsmul2 x' hx' s₁ x' hx',
    hself x hx, hself x' hx', halt x' hx' x hx]
  ring

theorem exists_int_of_isInteger_smul {F : Type} [Field F] [NumberField F] (d : 𝓞 F) (y : F)
    (h : IsLocalization.IsInteger (𝓞 F) (d • y)) : ∃ n : 𝓞 F, (n : F) = (d : F) * y := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, hn, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap]

theorem exists_alternating_bilinForm_eq_pairing : ∀ {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by
  intro F V _ _ _ _ hfin L hadd hsm P halt hPadd hPsmul x x' hx hx' hne
  have hP0 : ∀ y ∈ L, P 0 y = 0 := by
    intro y hy
    simpa using hPsmul 0 x hx y hy
  have hP0' : ∀ y ∈ L, P y 0 = 0 := by
    intro y hy
    have h0 : (0 : V) ∈ L := by simpa using hsm 0 x hx
    rw [halt y hy 0 h0, hP0 y hy, neg_zero]
  have hdne : ∀ d : (𝓞 F)⁰, ((d : 𝓞 F) : F) ≠ 0 := by
    intro d
    exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰ ![s, t]
    obtain ⟨n₀, hn₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) s (hd 0)
    obtain ⟨n₁, hn₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) t (hd 1)
    have hrel : (n₀ : F) • x + (n₁ : F) • x' = 0 := by
      rw [hn₀, hn₁, ← smul_smul, ← smul_smul, ← smul_add, hst, smul_zero]
    have e₀ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' n₀ n₁ 0 1
    have e₁ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' 1 0 n₀ n₁
    rw [hrel, hP0 _ (hadd _ (hsm 0 x hx) _ (hsm 1 x' hx'))] at e₀
    rw [hrel, hP0' _ (hadd _ (hsm 1 x hx) _ (hsm 0 x' hx'))] at e₁
    push_cast at e₀ e₁
    simp only [mul_one, mul_zero, sub_zero, one_mul, zero_mul] at e₀ e₁
    have h0 : (n₀ : F) = 0 := by
      rcases mul_eq_zero.mp e₀.symm with h | h
      · exact h
      · exact absurd h hne
    have h1 : (n₁ : F) = 0 := by
      rcases mul_eq_zero.mp e₁.symm with h | h
      · exact h
      · exact absurd h hne
    rw [hn₀] at h0
    rw [hn₁] at h1
    exact ⟨(mul_eq_zero.mp h0).resolve_left (hdne d), (mul_eq_zero.mp h1).resolve_left (hdne d)⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F V := by simp [hfin]
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2) F V, ⇑b = ![x, x'] :=
    ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩
  have hb0 : b 0 = x := by rw [hb]; rfl
  have hb1 : b 1 = x' := by rw [hb]; rfl
  let B : LinearMap.BilinForm F V := LinearMap.mk₂ F
    (fun z w => P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0))
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
  have hB : ∀ z w, B z w = P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0) :=
    fun _ _ => rfl
  have hBxx' : B x x' = P x x' := by
    rw [hB, ← hb0, ← hb1, b.repr_self, b.repr_self]
    simp
  refine ⟨B, fun z => by rw [hB]; ring, ?_⟩
  intro z hz w hw
  have hsum : ∀ v : V, v = b.repr v 0 • x + b.repr v 1 • x' := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two, hb0, hb1]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰
    ![b.repr z 0, b.repr z 1, b.repr w 0, b.repr w 1]
  obtain ⟨r₀, hr₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 0) (hd 0)
  obtain ⟨r₁, hr₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 1) (hd 1)
  obtain ⟨s₀, hs₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 0) (hd 2)
  obtain ⟨s₁, hs₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 1) (hd 3)
  set e : 𝓞 F := (d : 𝓞 F) with he
  have hez : (e : F) • z = (r₀ : F) • x + (r₁ : F) • x' := by
    calc (e : F) • z = (e : F) • (b.repr z 0 • x + b.repr z 1 • x') := congrArg _ (hsum z)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hr₀, hr₁]
  have hew : (e : F) • w = (s₀ : F) • x + (s₁ : F) • x' := by
    calc (e : F) • w = (e : F) • (b.repr w 0 • x + b.repr w 1 • x') := congrArg _ (hsum w)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hs₀, hs₁]
  have hPe : P ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * P z w) := by
    have a1 := hPsmul e z hz _ (hsm e w hw)
    have a2 := halt z hz _ (hsm e w hw)
    have a3 := hPsmul e w hw z hz
    have a4 := halt w hw z hz
    linear_combination a1 + (e : F) * a2 - (e : F) * a3 - (e : F) * (e : F) * a4
  have hBe : B ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * B z w) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have eP := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' r₀ r₁ s₀ s₁
  have eB := alternating_pairing_expand L hadd hsm (fun u v => B u v)
    (fun u _ v _ => by simp only [hB]; ring) (fun u₁ _ u₂ _ v _ => by rw [map_add, LinearMap.add_apply])
    (fun a u _ v _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]) hx hx' r₀ r₁ s₀ s₁
  rw [← hez, ← hew, hPe] at eP
  rw [← hez, ← hew, hBe, hBxx'] at eB
  have hee : (e : F) * (e : F) ≠ 0 := mul_ne_zero (hdne d) (hdne d)
  apply mul_left_cancel₀ hee
  linear_combination eP - eB

end GlobalTheory
end

open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_form_lattice_integrality : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by
  atlas_forward_decl GlobalTheory.exists_alternating_bilinForm_eq_pairing
end

section
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_coords_of_alt_ne_zero {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    {x x' : V} (h : B x x' ≠ 0) (v : V) : ∃ c c' : F, v = c • x + c' • x' := by
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun u => B u x') hst
    have h2 := congrArg (fun u => B x u) hst
    simp [hB] at h1 h2
    exact ⟨h1.resolve_right h, h2.resolve_right h⟩
  have hsp : Submodule.span F (Set.range ![x, x']) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hv : v ∈ Submodule.span F (Set.range ![x, x']) := by rw [hsp]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hv
  obtain ⟨a, b, hab⟩ := hv
  exact ⟨a, b, hab.symm⟩

theorem exists_fractionalIdeal_pairing_values :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V],
    Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) →
    ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 →
      ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v := by
  intro F V _ _ _ _ hV B hB L h0 hadd hsmul J hJ hLJ hJL v hv
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hJL t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro s ⟨z, hz, w, hw, rfl⟩
      simpa using hcon z hz w hw
    simpa using h2 h1
  obtain ⟨c, c', rfl⟩ := exists_coords_of_alt_ne_zero hV B hB hxx v
  let M : Submodule (𝓞 F) F :=
    { carrier := {t | ∃ z ∈ L, t = B z (c • x + c' • x')}
      zero_mem' := ⟨0, h0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨z + w, hadd z hz w hw, by rw [map_add B, LinearMap.add_apply]⟩
      smul_mem' := by
        rintro a _ ⟨z, hz, rfl⟩
        refine ⟨(a : F) • z, hsmul a z hz, ?_⟩
        rw [map_smul B, LinearMap.smul_apply, Algebra.smul_def, smul_eq_mul] }
  have hM : M ≤ ((FractionalIdeal.spanSingleton (𝓞 F)⁰ c * J +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ c' * J : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [FractionalIdeal.coe_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    refine Submodule.add_mem_sup ?_ ?_
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x hx)
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x' hx')
  refine ⟨⟨M, FractionalIdeal.isFractional_of_le hM⟩, ?_, fun t => Iff.rfl⟩
  intro hK0
  have hK := FractionalIdeal.eq_zero_iff.1 hK0
  have h1 := hK _ (show B x (c • x + c' • x') ∈ M from ⟨x, hx, rfl⟩)
  have h2 := hK _ (show B x' (c • x + c' • x') ∈ M from ⟨x', hx', rfl⟩)
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  simp [hB, hanti, hxx] at h1 h2
  apply hv
  simp [h1, h2]

end GlobalTheory
end

open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_form_ideal_generates_dual_vector : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 → ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v := by
  atlas_forward_decl GlobalTheory.exists_fractionalIdeal_pairing_values
end

section
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_fractionalIdeal_smul_mem_lattice_of_alternating
    {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    (L : Set V) (h0 : (0 : V) ∈ L) (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hBJ : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hspan t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨z, hz, w, hw, rfl⟩
      exact hcon z hz w hw
    rw [h2] at h1
    exact (Submodule.mem_bot _).1 h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : B (s • x + t • x') x' = 0 := by rw [hst]; simp
    have e2 : B x (s • x + t • x') = 0 := by rw [hst]; simp
    simp [hB, hxx] at e1 e2
    exact ⟨e1, e2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hvm : v ∈ Submodule.span F ({x, x'} : Set V) := by
    have : Set.range ![x, x'] = {x, x'} := by simp [Set.pair_comm]
    rw [← this, htop]; trivial
  obtain ⟨c, c', hc⟩ := Submodule.mem_span_pair.1 hvm
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ ∀ a : F, a • v ∈ L → a * t ∈ J := by
    by_cases hc0 : c = 0
    · have hc' : c' ≠ 0 := by
        rintro rfl
        apply hv
        rw [← hc, hc0]; simp
      refine ⟨B x v, ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc']
      · simpa using hBJ x hx _ ha
    · refine ⟨B v x', ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc0]
      · simpa using hBJ _ ha x' hx'
  let M : Submodule (𝓞 F) F :=
    { carrier := {a | a • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • v ∈ L
        rw [add_smul]; exact hadd _ ha _ hb
      zero_mem' := by
        show (0 : F) • v ∈ L
        rw [zero_smul]; exact h0
      smul_mem' := fun r a ha => by
        show ((r : F) * a) • v ∈ L
        rw [mul_smul]; exact hsmul r _ ha }
  have hM : IsFractional (𝓞 F)⁰ M := by
    apply FractionalIdeal.isFractional_of_le
      (J := FractionalIdeal.spanSingleton (𝓞 F)⁰ t⁻¹ * J)
    intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    exact ⟨a * t, ht a ha, by field_simp⟩
  refine ⟨⟨M, hM⟩, ?_, fun a => Iff.rfl⟩
  obtain ⟨d, n, hn⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c
  obtain ⟨d', n', hn'⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c'
  have hn1 : (n : F) = ((d : 𝓞 F) : F) * c := by
    simpa [Algebra.smul_def] using hn
  have hn2 : (n' : F) = ((d' : 𝓞 F) : F) * c' := by
    simpa [Algebra.smul_def] using hn'
  intro hz
  replace hz := FractionalIdeal.eq_zero_iff.1 hz
  have hmem : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v ∈ L := by
    have e : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v
        = ((d' : 𝓞 F) : F) • (n : F) • x + ((d : 𝓞 F) : F) • (n' : F) • x' := by
      rw [← hc, hn1, hn2]; module
    rw [e]
    exact hadd _ (hsmul _ _ (hsmul _ _ hx)) _ (hsmul _ _ (hsmul _ _ hx'))
  have h := hz _ hmem
  have hd : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hd' : ((d' : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d'
  exact mul_ne_zero hd hd' h

end GlobalTheory
end

open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_form_ideal_dual_vector_integral : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 → ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  atlas_forward_decl GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating
end

section
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_section_of_fractionalIdeal_values {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) {v : V} (K : FractionalIdeal (𝓞 F)⁰ F)
    (hK : K ≠ 0) (hKL : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) :
    ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by
  have hmul : K * K⁻¹ = 1 := mul_inv_cancel₀ hK
  have key : ∀ s ∈ K * K⁻¹, ∃ w : V, B w v = s ∧ ∀ t ∈ K, t • w ∈ L := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro k hk k' hk'
      obtain ⟨z, hz, rfl⟩ := (hKL k).1 hk
      refine ⟨k' • z, by simp [mul_comm], fun t ht => ?_⟩
      have h1 : t * k' ∈ K * K⁻¹ := FractionalIdeal.mul_mem_mul ht hk'
      rw [hmul, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨r, hr⟩ := h1
      rw [smul_smul, ← hr]
      exact hLsmul r z hz
    · rintro x y ⟨w, hw, hw'⟩ ⟨u, hu, hu'⟩
      refine ⟨w + u, by simp [hw, hu], fun t ht => ?_⟩
      rw [smul_add]
      exact hLadd _ (hw' t ht) _ (hu' t ht)
  refine key 1 ?_
  rw [hmul]
  exact FractionalIdeal.one_mem_one _

end GlobalTheory
end

open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_vector_pairing_one_ideal_multiple : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ {v : V} (K : FractionalIdeal (𝓞 F)⁰ F), K ≠ 0 →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by
  atlas_forward_decl GlobalTheory.exists_section_of_fractionalIdeal_values
end

section
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_coords_of_alt_pair {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    {v w : V} (hv : v ≠ 0) (hw : B w v = 1) (u : V) : ∃ p q : F, p • v + q • w = u := by
  have hli : LinearIndependent F ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : B (s • v + t • w) v = 0 := by rw [h]; simp
    have ht : t = 0 := by simpa [hB, hw] using h1
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at h
    exact ⟨h.resolve_right hv, rfl⟩
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hr : Set.range ![v, w] = {v, w} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [hr] at hsp
  have hu : u ∈ Submodule.span F ({v, w} : Set V) := by rw [hsp]; trivial
  exact Submodule.mem_span_pair.mp hu

theorem lattice_eq_ideal_sum_and_mul_eq :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v w : V}, v ≠ 0 → ∀ (I K : FractionalIdeal (𝓞 F)⁰ F), (∀ a : F, a ∈ I ↔ a • v ∈ L) →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → B w v = 1 → (∀ t ∈ K, t • w ∈ L) →
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J := by
  intro F V _ _ _ _ hV B hB L _ hadd hsmul J hJ hJs v w hv I K hI hK hw hwL
  have hvw : B v w = -1 := by
    have h := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, hw] at h
    linear_combination h
  have hmem : ∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, q, rfl⟩ := exists_coords_of_alt_pair hV B hB hv hw x
      have hq : q ∈ K := (hK q).2 ⟨_, hx, by simp [hB, hw]⟩
      refine ⟨p, (hI p).2 ?_, q, hq, rfl⟩
      have h1 := hadd _ hx _ (hsmul (-1) _ (hwL q hq))
      simpa using h1
    · rintro ⟨a, ha, t, ht, rfl⟩
      exact hadd _ ((hI a).1 ha) _ (hwL t ht)
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · rw [FractionalIdeal.mul_le]
    intro a ha t ht
    have h := hJ _ (hwL t ht) _ ((hI a).1 ha)
    simpa [hw, mul_comm] using h
  · intro t ht
    have h := hJs t ht
    have hle : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}
        ≤ ((I * K : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, z', hz', rfl⟩
      obtain ⟨a, ha, s, hs, rfl⟩ := (hmem z).1 hz
      obtain ⟨a', ha', s', hs', rfl⟩ := (hmem z').1 hz'
      have e : B (a • v + s • w) (a' • v + s' • w) = a' * s - a * s' := by
        simp [hB, hw, hvw]; ring
      rw [e]
      exact Submodule.sub_mem _ (FractionalIdeal.mul_mem_mul ha' hs)
        (FractionalIdeal.mul_mem_mul ha hs')
    exact hle h

end GlobalTheory
end

open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_form_ideal_pair_of_vectors : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v w : V}, v ≠ 0 → ∀ (I K : FractionalIdeal (𝓞 F)⁰ F), (∀ a : F, a ∈ I ↔ a • v ∈ L) →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → B w v = 1 → (∀ t ∈ K, t • w ∈ L) →
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J := by
  atlas_forward_decl GlobalTheory.lattice_eq_ideal_sum_and_mul_eq
end

section
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_mem_spanSingleton_mul_inv_add_eq_one {F : Type} [Field F] [NumberField F]
    (Y N : FractionalIdeal (𝓞 F)⁰ F) (hY : Y ≠ 0) (hN : N ≠ 0) (hN1 : N ≤ 1) :
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 := by
  obtain ⟨N', rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hN1
  obtain ⟨a, Y', ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul Y
  have hA : algebraMap (𝓞 F) F a ≠ 0 := by
    intro h; exact ha ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hAi : (algebraMap (𝓞 F) F a)⁻¹ ≠ 0 := inv_ne_zero hA
  have hS : FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F a)⁻¹ ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hAi
  have hY' : Y' ≠ ⊥ := by
    rintro rfl; apply hY; simp
  have hN' : N' ≠ ⊥ := by
    rintro rfl; apply hN; simp
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (I := Y' * N') (J := Y')
    Ideal.mul_le_left (mul_ne_zero hY' hN')
  have key : (Y' : FractionalIdeal (𝓞 F)⁰ F) * N' +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F r) = Y' := by
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_sup, hr]
  have hY'0 : (Y' : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hY'
  have hrY : r ∈ Y' := by
    rw [← hr]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self r)
  refine ⟨(algebraMap (𝓞 F) F a)⁻¹ * algebraMap (𝓞 F) F r, ?_, ?_⟩
  · exact FractionalIdeal.mem_singleton_mul.mpr
      ⟨algebraMap (𝓞 F) F r, (FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hrY, rfl⟩, rfl⟩
  · rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv, mul_mul_mul_comm,
      mul_comm (FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F a)⁻¹),
      inv_mul_cancel₀ hS, one_mul]
    have h2 := congrArg (· * (Y' : FractionalIdeal (𝓞 F)⁰ F)⁻¹) key
    simp only [add_mul, mul_inv_cancel₀ hY'0] at h2
    rw [mul_comm (Y' : FractionalIdeal (𝓞 F)⁰ F) _, mul_assoc, mul_inv_cancel₀ hY'0, mul_one] at h2
    rw [add_comm]; exact h2

end GlobalTheory
end

open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_coprime_element_exists : ∀ {F : Type} [Field F] [NumberField F] (Y N : FractionalIdeal (𝓞 F)⁰ F), Y ≠ 0 → N ≠ 0 → N ≤ 1 →
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 := by
  atlas_forward_decl GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AltLattice

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]

theorem exists_bilin_ext (hV : Module.finrank F V = 2) (L : Set V)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (P : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x)
    (hadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x')
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x')
    {x x' : V} (hx : x ∈ L) (hx' : x' ∈ L) (hP : P x x' ≠ 0) :
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w :=
  GlobalTheory.T.alternating_form_lattice_integrality hV L hLadd hLsmul P halt hadd hsmul hx hx' hP

theorem fracIdeal_pairing (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V)
    (hB : ∀ z, B z z = 0) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hval : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v :=
  GlobalTheory.T.lattice_form_ideal_generates_dual_vector hV B hB L hL0 hLadd hLsmul J hJ hval hspan hv

theorem fracIdeal_line (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V)
    (hB : ∀ z, B z z = 0) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hval : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L :=
  GlobalTheory.T.lattice_form_ideal_dual_vector_integral hV B hB L hL0 hLadd hLsmul J hJ hval hspan hv

theorem exists_section (B : LinearMap.BilinForm F V) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    {v : V} (K : FractionalIdeal (𝓞 F)⁰ F) (hK : K ≠ 0) (hKL : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) :
    ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L :=
  GlobalTheory.T.lattice_vector_pairing_one_ideal_multiple B L hL0 hLadd hLsmul K hK hKL

theorem decomp_of_section (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V)
    (hB : ∀ z, B z z = 0) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hval : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v w : V} (hv : v ≠ 0) (I K : FractionalIdeal (𝓞 F)⁰ F) (hI : ∀ a : F, a ∈ I ↔ a • v ∈ L)
    (hK : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) (hw : B w v = 1) (hwL : ∀ t ∈ K, t • w ∈ L) :
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J :=
  GlobalTheory.T.lattice_form_ideal_pair_of_vectors hV B hB L hL0 hLadd hLsmul J hval hspan hv I K hI hK hw hwL

theorem exists_mem_coprime (Y N : FractionalIdeal (𝓞 F)⁰ F) (hY : Y ≠ 0) (hN : N ≠ 0) (hN1 : N ≤ 1) :
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 :=
  GlobalTheory.T.fractional_ideal_coprime_element_exists Y N hY hN hN1

theorem exists_comb_eq (A B C : FractionalIdeal (𝓞 F)⁰ F) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ∃ α β : F, FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * B = C := by
  have hCA : C * A⁻¹ ≠ 0 := mul_ne_zero hC (inv_ne_zero hA)
  obtain ⟨α, hα, hα0⟩ : ∃ α ∈ C * A⁻¹, α ≠ 0 := by
    by_contra h
    push_neg at h
    apply hCA
    ext t
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h t, fun ht => ht ▸ Submodule.zero_mem ((C * A⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)⟩
  set N := FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A * C⁻¹ with hNdef
  have hsα : FractionalIdeal.spanSingleton (𝓞 F)⁰ α ≤ C * A⁻¹ :=
    FractionalIdeal.spanSingleton_le_iff_mem.2 hα
  have hN1 : N ≤ 1 := by
    calc N ≤ C * A⁻¹ * A * C⁻¹ := by rw [hNdef]; exact mul_le_mul_left (mul_le_mul_left hsα A) C⁻¹
      _ = 1 := by
        rw [_root_.mul_assoc C, inv_mul_cancel₀ hA, _root_.mul_one, mul_inv_cancel₀ hC]
  have hN0 : N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hα0) hA) (inv_ne_zero hC)
  obtain ⟨β, -, hβN⟩ := exists_mem_coprime (C * B⁻¹) N (mul_ne_zero hC (inv_ne_zero hB)) hN0 hN1
  refine ⟨α, β, ?_⟩
  have e1 : N * C = FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A := by
    rw [hNdef, _root_.mul_assoc _ C⁻¹, inv_mul_cancel₀ hC, _root_.mul_one]
  have e2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ β * (C * B⁻¹)⁻¹ * C =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ β * B := by
    rw [mul_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_comm B C, ← _root_.mul_assoc C⁻¹,
      inv_mul_cancel₀ hC, _root_.one_mul]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * B
      = (FractionalIdeal.spanSingleton (𝓞 F)⁰ β * (C * B⁻¹)⁻¹ + N) * C := by
        rw [add_mul, e1, e2, add_comm]
    _ = C := by rw [hβN, _root_.one_mul]

theorem pairing_change (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0) (L : Set V) {v w : V}
    (hw : B w v = 1) (I K : FractionalIdeal (𝓞 F)⁰ F)
    (hL : ∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) (α β t : F) :
    (∃ z ∈ L, t = B z (α • v + β • w)) ↔
      t ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ α * K + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * I := by
  have hvw : B v w = -1 := by
    have := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, hw] at this
    linear_combination this
  have hval : ∀ a s : F, B (a • v + s • w) (α • v + β • w) = α * s + β * (-a) := by
    intro a s
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB, hw, hvw]
    ring
  show _ ↔ t ∈ ((FractionalIdeal.spanSingleton (𝓞 F)⁰ α * K + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * I :
    FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
  rw [FractionalIdeal.coe_add, Submodule.add_eq_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha, s, hs, rfl⟩ := (hL z).1 hz
    rw [hval]
    exact ⟨α * s, FractionalIdeal.mem_singleton_mul.2 ⟨s, hs, rfl⟩, β * (-a),
      FractionalIdeal.mem_singleton_mul.2 ⟨-a, Submodule.neg_mem (I : Submodule (𝓞 F) F) ha, rfl⟩, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨s, hs, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hp
    obtain ⟨b, hb, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hq
    exact ⟨(-b) • v + s • w, (hL _).2 ⟨-b, Submodule.neg_mem (I : Submodule (𝓞 F) F) hb, s, hs, rfl⟩,
      by rw [hval, neg_neg]⟩

end GlobalTheory.AltLattice

namespace GlobalTheory.AltLattice

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]

theorem exists_sympl_basis (hV : Module.finrank F V = 2) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (M 𝔟 : FractionalIdeal (𝓞 F)⁰ F) (hM : M ≠ 0) (h𝔟 : 𝔟 ≠ 0) (P : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x)
    (hadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x')
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x')
    (hval : ∀ x ∈ L, ∀ x' ∈ L, P x x' ∈ M * 𝔟)
    (hspan : ∀ t ∈ M * 𝔟, t ∈ Submodule.span (𝓞 F) {t | ∃ x ∈ L, ∃ x' ∈ L, t = P x x'}) :
    ∃ ω₁ ω₂ : V, (∀ x, x ∈ L ↔ ∃ m ∈ M, ∃ β ∈ 𝔟, x = m • ω₁ + β • ω₂) ∧
      ∀ m ∈ M, ∀ β ∈ 𝔟, ∀ m' ∈ M, ∀ β' ∈ 𝔟,
        P (m • ω₁ + β • ω₂) (m' • ω₁ + β' • ω₂) = β * m' - m * β' := by
  have hJ : M * 𝔟 ≠ 0 := mul_ne_zero hM h𝔟
  obtain ⟨x, hx, x', hx', hP⟩ : ∃ x ∈ L, ∃ x' ∈ L, P x x' ≠ 0 := by
    by_contra h
    push_neg at h
    apply hJ
    ext t
    rw [FractionalIdeal.mem_zero_iff]
    refine ⟨fun ht => ?_, fun ht => ?_⟩
    swap
    · subst ht; exact Submodule.zero_mem ((M * 𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
    have h1 := hspan t ht
    have hs : {t | ∃ x ∈ L, ∃ x' ∈ L, t = P x x'} ⊆ ({0} : Set F) := by
      rintro _ ⟨z, hz, w, hw, rfl⟩; exact h z hz w hw
    have h2 := Submodule.span_mono (R := 𝓞 F) hs h1
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at h2
    exact h2
  obtain ⟨B, hB, hPB⟩ := exists_bilin_ext hV L hLadd hLsmul P halt hadd hsmul hx hx' hP
  have hvalB : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ M * 𝔟 := fun z hz w hw => hPB z hz w hw ▸ hval z hz w hw
  have hsetB : {t | ∃ x ∈ L, ∃ x' ∈ L, t = P x x'} = {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} := by
    ext t; constructor
    · rintro ⟨z, hz, w, hw, rfl⟩; exact ⟨z, hz, w, hw, hPB z hz w hw⟩
    · rintro ⟨z, hz, w, hw, rfl⟩; exact ⟨z, hz, w, hw, (hPB z hz w hw).symm⟩
  have hspanB : ∀ t ∈ M * 𝔟, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} :=
    fun t ht => hsetB ▸ hspan t ht
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hP; rw [hPB 0 hx x' hx']; simp
  have hvw : ∀ v w : V, B w v = 1 → B v w = -1 := fun v w h => by
    have := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, h] at this
    linear_combination this

  obtain ⟨K₀, hK₀, hK₀L⟩ := fracIdeal_pairing hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hx0
  obtain ⟨I₀, hI₀, hI₀L⟩ := fracIdeal_line hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hx0
  obtain ⟨w₀, hw₀, hw₀L⟩ := exists_section B L hL0 hLadd hLsmul K₀ hK₀ hK₀L
  obtain ⟨hL₀, -⟩ := decomp_of_section hV B hB L hL0 hLadd hLsmul _ hvalB hspanB hx0 I₀ K₀ hI₀L hK₀L hw₀ hw₀L

  obtain ⟨α, β, hαβ⟩ := exists_comb_eq K₀ I₀ 𝔟 hK₀ hI₀ h𝔟
  set v := α • x + β • w₀ with hvdef
  have hv : v ≠ 0 := by
    intro h0
    have h1 : B w₀ v = α := by
      simp [hvdef, hB, hw₀]
    have h2 : B x v = -β := by
      simp [hvdef, hB, hvw x w₀ hw₀]
    rw [h0] at h1 h2
    simp only [map_zero] at h1 h2
    have hα : α = 0 := h1.symm
    have hβ : β = 0 := by linear_combination h2
    apply h𝔟
    rw [← hαβ, hα, hβ]; simp
  obtain ⟨K, hK, hKL⟩ := fracIdeal_pairing hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hv
  obtain ⟨I, hI, hIL⟩ := fracIdeal_line hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hv
  obtain ⟨w, hw, hwL⟩ := exists_section B L hL0 hLadd hLsmul K hK hKL
  obtain ⟨hL, hIK⟩ := decomp_of_section hV B hB L hL0 hLadd hLsmul _ hvalB hspanB hv I K hIL hKL hw hwL
  have hK𝔟 : K = 𝔟 := by
    ext t
    rw [hKL t, pairing_change B hB L hw₀ I₀ K₀ hL₀ α β t, hαβ]
  have hIM : I = M := by
    rw [hK𝔟] at hIK
    exact mul_right_cancel₀ h𝔟 hIK
  subst hK𝔟 hIM
  refine ⟨v, w, hL, ?_⟩
  intro m hm b hb m' hm' b' hb'
  rw [hPB _ ((hL _).2 ⟨m, hm, b, hb, rfl⟩) _ ((hL _).2 ⟨m', hm', b', hb', rfl⟩)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB, hw, hvw v w hw]
  ring

end GlobalTheory.AltLattice

namespace GlobalTheory.AltLattice

theorem dualLat_mul_inv {F : Type} [Field F] [NumberField F] (𝔞 𝔟 : FracId F) :
    dualLat (𝔞 * 𝔟⁻¹) = dualLat 𝔞 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  simp only [dualLat, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ, FractionalIdeal.dual_eq_mul_inv ℤ ℚ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
    mul_inv, inv_inv]
  exact (_root_.mul_assoc _ _ _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := by
  intro E _ _ _ c y _ 𝔞 𝔟 P halt hadd hsmul hval hspan
  have hsm : ∀ (a : FR E) (x : E), a • x = (a : E) * x := fun _ _ => rfl
  have hV : Module.finrank (FR E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hM : dualLat 𝔞 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero 𝔞)
  rw [dualLat_mul_inv] at hval hspan
  obtain ⟨ω₁, ω₂, h1, h2⟩ := exists_sympl_basis (F := FR E) (V := E) hV (lattice c y)
    (latticeSub c y).zero_mem (fun x hx x' hx' => (latticeSub c y).add_mem hx hx')
    (fun a x hx => by rw [hsm]; exact mul_mem_lattice (algebraMap_mem_orderC c a) hx)
    (dualLat 𝔞) 𝔟 hM (Units.ne_zero 𝔟) P halt hadd
    (fun a x hx x' hx' => by rw [hsm]; exact hsmul a x hx x' hx') hval hspan
  refine ⟨ω₁, ω₂, fun x => ?_, fun m hm β hβ m' hm' β' hβ' => ?_⟩
  · have h := h1 x
    simp only [hsm] at h
    exact h
  · have h := h2 m hm β hβ m' hm' β' hβ'
    simp only [hsm] at h
    exact h

end GlobalTheory.AltLattice
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_pairing_on_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := by
  atlas_forward_decl GlobalTheory.AltLattice.main
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rescaled_uniformization : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (lam : Fin g → ℂ),
    (∀ j, lam j ≠ 0) → ∃ u' : HolUnif A Lb g, (∀ w, u'.ex w = u.ex (fun j ↦ lam j * w j)) ∧
      (∀ (d : Fin g → ℝ) χ, u.IsAH (Matrix.diagonal fun j ↦ (d j : ℂ)) χ →
        ∃ χ', u'.IsAH (Matrix.diagonal fun j ↦ ((d j * ‖lam j‖ ^ 2 : ℝ) : ℂ)) χ') ∧
      (∀ W v, u'.IsDiff W v ↔ u.IsDiff (fun j ↦ lam j * W j) v) := by
  first | exact @GlobalTheory.holUnif_rescale | exact GlobalTheory.holUnif_rescale | (intros; apply GlobalTheory.holUnif_rescale <;> assumption)
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusFormPf

theorem embOfCM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := GlobalTheory.T.exists_real_embedding_ordering

theorem realEmb_indep : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := GlobalTheory.T.real_embeddings_linearly_independent

theorem riemannForm_of_unif : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∃ P : u.Λ → u.Λ → F, (∀ l l' : u.Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : u.Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : u.Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : u.Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : u.Λ, P l l' ∈ dualLat 𝔠) ∧
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := GlobalTheory.T.diagonal_appell_humbert_real_mult

theorem steinitz_sympl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := GlobalTheory.T.alternating_pairing_on_lattice

theorem holUnif_rescale : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (lam : Fin g → ℂ),
    (∀ j, lam j ≠ 0) → ∃ u' : HolUnif A Lb g, (∀ w, u'.ex w = u.ex (fun j ↦ lam j * w j)) ∧
      (∀ (d : Fin g → ℝ) χ, u.IsAH (Matrix.diagonal fun j ↦ (d j : ℂ)) χ →
        ∃ χ', u'.IsAH (Matrix.diagonal fun j ↦ ((d j * ‖lam j‖ ^ 2 : ℝ) : ℂ)) χ') ∧
      (∀ W v, u'.IsDiff W v ↔ u.IsDiff (fun j ↦ lam j * W j) v) := GlobalTheory.T.rescaled_uniformization

end GlobalTheory.TorusFormPf

namespace GlobalTheory.TorusFormPf

theorem lattice_add {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {y : (Af E)ˣ} {x x' : E}
    (hx : x ∈ lattice c y) (hx' : x' ∈ lattice c y) : x + x' ∈ lattice c y := by
  simp only [lattice, Set.mem_setOf_eq, map_add, add_mul] at *
  exact Subring.add_mem _ hx hx'

theorem lattice_smul {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {y : (Af E)ˣ} {x : E}
    (a : 𝓞 (FR E)) (hx : x ∈ lattice c y) : ((a : FR E) : E) * x ∈ lattice c y := by
  have := mul_mem_lattice (algebraMap_mem_orderC c a) hx
  convert this using 2
  first | rfl | simp [IsScalarTower.algebraMap_apply (OF E) (FR E) E] | exact (IsScalarTower.algebraMap_apply (OF E) (FR E) E a).symm

theorem torusForm : TorusForm := by
  intro E _ _ _ I _ 𝔞 𝔟 φ c y hCM hc z hz X U
  obtain ⟨e, he⟩ := embOfCM E I φ hCM U.e
  have hreal : ∀ j (x : FR E), starRingEnd ℂ (φ (U.e j) (x : E)) = φ (U.e j) (x : E) := by
    intro j x; rw [← he]; exact Complex.conj_ofReal _
  set D : E → Fin (Module.finrank ℚ (FR E)) → ℂ := fun x j ↦ defCoord φ z x (U.e j) with hD
  have hDadd : ∀ x x', D (x + x') = D x + D x' := by
    intro x x'; funext j; simp only [hD, defCoord, map_add, Pi.add_apply]; ring
  have hDsmul : ∀ (a : FR E) x, D ((a : E) * x) = fun j ↦ (e j a : ℂ) * D x j := by
    intro a x; funext j; simp only [hD, defCoord, map_mul]; rw [hreal j a, ← he]; ring
  have hact : ∀ (a : 𝓞 (FR E)) w, U.u.ex (fun j ↦ (e j (a : FR E) : ℂ) * w j) = U.u.ex w ≫ X.rm.act a := by
    intro a w; simpa only [he] using U.act a w
  obtain ⟨χ, hAH⟩ := U.ah
  obtain ⟨P, hPalt, hPadd, hPsmul, hPtr, hPmem, hPspan⟩ := riemannForm_of_unif (FR E) (𝔞 * 𝔟⁻¹) X U.c U.pos U.u e hact
    (fun j ↦ U.h (U.e j)) χ hAH
  have hDmem : ∀ x ∈ lattice c y, D x ∈ U.u.Λ := fun x hx ↦ (U.lat _).2 ⟨x, hx, rfl⟩
  classical
  let PL : E → E → FR E := fun x x' ↦
    if hx : x ∈ lattice c y ∧ x' ∈ lattice c y then P ⟨D x, hDmem x hx.1⟩ ⟨D x', hDmem x' hx.2⟩ else 0
  have hPL : ∀ x (hx : x ∈ lattice c y) x' (hx' : x' ∈ lattice c y),
      PL x x' = P ⟨D x, hDmem x hx⟩ ⟨D x', hDmem x' hx'⟩ := by
    intro x hx x' hx'; simp only [PL, dif_pos (And.intro hx hx')]
  obtain ⟨ω₁, ω₂, hL, hPω⟩ := steinitz_sympl E c y hc 𝔞 𝔟 PL
    (by intro x hx x' hx'; rw [hPL x hx x' hx', hPL x' hx' x hx]; exact hPalt _ _)
    (by
      intro x₁ h₁ x₂ h₂ x' h'
      rw [hPL _ (lattice_add h₁ h₂) x' h', hPL x₁ h₁ x' h', hPL x₂ h₂ x' h', ← hPadd]
      congr 1; exact Subtype.ext (hDadd x₁ x₂))
    (by
      intro a x hx x' hx'
      rw [hPL _ (lattice_smul a hx) x' hx', hPL x hx x' hx']
      exact hPsmul a _ _ _ (hDsmul (a : FR E) x))
    (by intro x hx x' hx'; rw [hPL x hx x' hx']; exact hPmem _ _)
    (by
      intro t ht
      have := hPspan t ht
      refine Submodule.span_mono ?_ this
      rintro s ⟨l, l', rfl⟩
      obtain ⟨x, hx, hxl⟩ := (U.lat l).1 l.2
      obtain ⟨x', hx', hxl'⟩ := (U.lat l').1 l'.2
      refine ⟨x, hx, x', hx', ?_⟩
      rw [hPL x hx x' hx']
      congr 1 <;> apply Subtype.ext <;> assumption)
  set A : Fin (Module.finrank ℚ (FR E)) → ℂ := D ω₁ with hA
  set B : Fin (Module.finrank ℚ (FR E)) → ℂ := D ω₂ with hB
  have hDlin : ∀ m β : FR E, D ((m : E) * ω₁ + (β : E) * ω₂) = fun j ↦ (e j m : ℂ) * A j + (e j β : ℂ) * B j := by
    intro m β; rw [hDadd, hDsmul, hDsmul]; rfl
  have hmemL : ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, (m : E) * ω₁ + (β : E) * ω₂ ∈ lattice c y :=
    fun m hm β hβ ↦ (hL _).2 ⟨m, hm, β, hβ, rfl⟩
  obtain ⟨β₀, hβ₀, hβ₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ 𝔟.ne_zero (FractionalIdeal.coeToSubmodule_eq_bot.1 h))
  have hdual0 : dualLat 𝔞 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero
  obtain ⟨m₀, hm₀, hm₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ hdual0 (FractionalIdeal.coeToSubmodule_eq_bot.1 h))
  have h0a : (0 : FR E) ∈ dualLat 𝔞 := (dualLat 𝔞 : Submodule (𝓞 (FR E)) (FR E)).zero_mem
  have h0b : (0 : FR E) ∈ 𝔟.elt := 𝔟.elt.zero_mem
  have hkey : ∀ x : 𝓞 (FR E), ∑ j, e j (x : FR E) * ((e j β₀ * e j m₀) *
      (U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im - 2 * e j (U.c : FR E))) = 0 := by
    intro x
    have hxβ : (x : FR E) * β₀ ∈ 𝔟.elt := by
      have := 𝔟.elt.smul_mem x hβ₀; rwa [Algebra.smul_def] at this
    have m1 := hmemL 0 h0a _ hxβ
    have m2 := hmemL m₀ hm₀ 0 h0b
    have htr := hPtr ⟨_, hDmem _ m1⟩ ⟨_, hDmem _ m2⟩
    rw [← hPL _ m1 _ m2, hPω 0 h0a _ hxβ m₀ hm₀ 0 h0b, GlobalTheory.trace_eq_sum_realEmbeddings, ← e.sum_comp] at htr
    simp only [hDlin, Complex.im_sum] at htr
    have hl : ∀ j, ((U.h (U.e j) : ℂ) * ((((e j 0 : ℝ) : ℂ) * A j + ((e j ((x : FR E) * β₀) : ℝ) : ℂ) * B j) *
        starRingEnd ℂ (((e j m₀ : ℝ) : ℂ) * A j + ((e j 0 : ℝ) : ℂ) * B j))).im =
        e j (x : FR E) * (e j β₀ * e j m₀ * (U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im)) := by
      intro j
      have : (U.h (U.e j) : ℂ) * ((((e j 0 : ℝ) : ℂ) * A j + ((e j ((x : FR E) * β₀) : ℝ) : ℂ) * B j) *
          starRingEnd ℂ (((e j m₀ : ℝ) : ℂ) * A j + ((e j 0 : ℝ) : ℂ) * B j)) =
          ((U.h (U.e j) * e j (x : FR E) * e j β₀ * e j m₀ : ℝ) : ℂ) * (B j * starRingEnd ℂ (A j)) := by
        simp only [map_zero, map_mul, map_add, Complex.ofReal_zero, Complex.conj_ofReal, zero_mul, zero_add, add_zero]
        push_cast; ring
      rw [this, Complex.im_ofReal_mul]; ring
    simp only [hl] at htr
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib] at htr
    rw [← htr]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [map_mul, map_sub, map_zero, mul_zero, sub_zero]
    ring
  have hk : ∀ j, U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im = 2 * e j (U.c : FR E) := by
    have hz := realEmb_indep (FR E) (fun σ ↦ (e (e.symm σ) β₀ * e (e.symm σ) m₀) *
      (U.h (U.e (e.symm σ)) * (B (e.symm σ) * starRingEnd ℂ (A (e.symm σ))).im - 2 * e (e.symm σ) (U.c : FR E))) (by
        intro x
        rw [← e.sum_comp]
        simp only [Equiv.symm_apply_apply]
        rw [← hkey x]
        exact Finset.sum_congr rfl fun j _ ↦ by ring)
    intro j
    have := congrFun hz (e j)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
    have hne : e j β₀ * e j m₀ ≠ 0 := mul_ne_zero ((map_ne_zero _).2 hβ₀0) ((map_ne_zero _).2 hm₀0)
    have := (mul_eq_zero.1 this).resolve_left hne
    linarith
  have hhpos : ∀ j, 0 < U.h (U.e j) := by
    intro j
    have hne : (Pi.single j (1 : ℂ) : Fin (Module.finrank ℚ (FR E)) → ℂ) ≠ 0 := fun h ↦ by simpa using congrFun h j
    have := hAH.2.1 _ hne
    simpa [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply] using this
  have hIm : ∀ j, 0 < (B j * starRingEnd ℂ (A j)).im := by
    intro j
    have hc := U.pos (e j)
    have : 0 < U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im := by rw [hk j]; linarith
    exact pos_of_mul_pos_right this (le_of_lt (hhpos j))
  have hA0 : ∀ j, A j ≠ 0 := by
    intro j h; have := hIm j; rw [h] at this; simp at this
  set τ : (FR E →+* ℝ) → ℂ := fun σ ↦ B (e.symm σ) / A (e.symm σ) with hτdef
  set lam : Fin (Module.finrank ℚ (FR E)) → ℂ := fun j ↦ A j / (2 * Real.pi * Complex.I) with hlamdef
  have hτ : ∀ j, τ (e j) = B j / A j := by intro j; simp [hτdef]
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hlam : ∀ j, lam j ≠ 0 := fun j ↦ div_ne_zero (hA0 j) h2pi
  have hτim : ∀ j, (τ (e j)).im = (B j * starRingEnd ℂ (A j)).im / Complex.normSq (A j) := by
    intro j; rw [hτ, Complex.div_im]; simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  obtain ⟨u', hex, hAH', hdiff⟩ := holUnif_rescale X.A (X.diag U.c) _ U.u lam hlam
  have hform : ∀ m β : FR E, (fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) =
      D ((m : E) * ω₁ + (β : E) * ω₂) := by
    intro m β; rw [hDlin]; funext j; rw [hτ]; simp only [hlamdef]; have hAj := hA0 j; field_simp; try ring
  have hlat : ∀ w, w ∈ U.u.Λ ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
      w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j))) := by
    intro w
    rw [U.lat]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨m, hm, β, hβ, rfl⟩ := (hL x).1 hx
      exact ⟨m, hm, β, hβ, (hform m β).symm⟩
    · rintro ⟨m, hm, β, hβ, rfl⟩
      exact ⟨_, hmemL m hm β hβ, hform m β⟩
  refine ⟨e, τ, lam, he, fun σ ↦ ?_, hlam, hlat, ?_⟩
  · have := hτim (e.symm σ)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
    exact div_pos (hIm _) (Complex.normSq_pos.2 (hA0 _))
  · intro δ hδ
    refine ⟨U.c, u', U.pos, ?_, ?_, ?_, ?_⟩
    · intro w
      have hk' : w ∈ u'.Λ ↔ (fun j ↦ lam j * w j) ∈ U.u.Λ := by rw [← u'.ker, ← U.u.ker, hex]
      rw [hk', hlat]
      refine exists_congr fun m ↦ and_congr_right fun _ ↦ exists_congr fun β ↦ and_congr_right fun _ ↦ ?_
      constructor
      · intro h; funext j; exact mul_left_cancel₀ (hlam j) (congrFun h j)
      · intro h; rw [h]
    · intro a w
      rw [hex, hex, ← hact]
      congr 1; funext j; ring
    · obtain ⟨χ', h'⟩ := hAH' (fun j ↦ U.h (U.e j)) χ hAH
      refine ⟨χ', ?_⟩
      have hm : (fun i ↦ (((2 * e i (U.c : FR E) / (4 * Real.pi ^ 2 * (τ (e i)).im)) : ℝ) : ℂ)) =
          fun j ↦ ((U.h (U.e j) * ‖lam j‖ ^ 2 : ℝ) : ℂ) := by
        funext j
        congr 1
        have hn : ‖lam j‖ ^ 2 = Complex.normSq (A j) / (4 * Real.pi ^ 2) := by
          rw [hlamdef, norm_div, div_pow, Complex.sq_norm]
          congr 1
          simp [Complex.norm_mul, abs_of_pos Real.pi_pos]; ring
        rw [hn, hτim, ← hk j]
        have := hIm j
        have := Complex.normSq_pos.2 (hA0 j)
        field_simp
      rw [hm]; exact h'
    · intro v W hW
      have hW' : ∀ i, U.u.IsDiff (fun j ↦ lam j * W i j) (v i).hom := fun i ↦ (hdiff _ _).1 (hW i)
      rw [hδ v (Matrix.of fun i j ↦ lam j * W i j) hW']
      have hdet : (Matrix.of fun i j ↦ lam j * W i j).det = W.det * ∏ j, lam j := by
        have : (Matrix.of fun i j ↦ lam j * W i j) = W * Matrix.diagonal lam := by
          ext i j; simp [Matrix.mul_diagonal, mul_comm]
        rw [this, Matrix.det_mul, Matrix.det_diagonal]
      rw [hdet]
      have hprod : ∏ j, lam j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hlam j
      have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) = ((Real.sqrt |(discr (FR E) : ℝ)| *
          (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 (FR E))⁰ (FR E)) : ℝ) : ℝ) : ℂ) := by
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, Real.sqrt_eq_rpow]
      rw [hΩ]; field_simp

end GlobalTheory.TorusFormPf
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_form_statement_holds : TorusForm := by
  atlas_forward_decl GlobalTheory.TorusFormPf.torusForm
end
