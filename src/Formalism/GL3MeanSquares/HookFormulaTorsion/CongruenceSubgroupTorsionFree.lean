import Mathlib
import Formalism.GL3MeanSquares.CongruenceTorsion
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferenceStableUnderAction
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions

namespace Formalism.HermitianLattices.StabilizerLevels
namespace PfB

section S1
open NumberField IsDedekindDomain
open scoped TensorProduct




section sep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (w : HeightOneSpectrum (𝓞 F))

noncomputable def owHom :
    (w.adicCompletionIntegers F) →+* E ⊗[F] w.adicCompletion F :=
  (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := w.adicCompletion F)).toRingHom.comp
    (w.adicCompletionIntegers F).subtype

local notation "O" => (HeightOneSpectrum.adicCompletionIntegers F w)

theorem sepLemma (g : ℕ) (hgw : (g : 𝓞 F) ∈ w.asIdeal) :
    ∃ (A : Subring (E ⊗[F] w.adicCompletion F)),
      Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring ≤ A ∧
      (⨅ m : ℕ, (Ideal.span {(g : A)}) ^ m) = ⊥ := by
  classical
  let _ : Algebra (w.adicCompletionIntegers F) (E ⊗[F] w.adicCompletion F) := (owHom (E := E) w).toAlgebra
  let ι : 𝓞 E →+* E ⊗[F] w.adicCompletion F := (Formalism.UG.inclE (F := F) (E := E) (w.adicCompletion F)).comp (algebraMap (𝓞 E) E)
  let bs := NumberField.RingOfIntegers.basis E
  let s : Set (E ⊗[F] w.adicCompletion F) := Set.range (fun i => ι (bs i))
  have hsfin : s.Finite := Set.finite_range _
  have hint : ∀ x ∈ s, IsIntegral O x := by
    rintro _ ⟨i, rfl⟩
    have h1 : IsIntegral ℤ (bs i) := Algebra.IsIntegral.isIntegral _
    exact h1.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)
  have hfg := fg_adjoin_of_finite hsfin hint
  let A := Algebra.adjoin O s
  have : Module.Finite O A := Module.Finite.iff_fg.2 hfg
  have hιA : ∀ x : 𝓞 E, ι x ∈ A := by
    intro x
    rw [← bs.sum_repr x, map_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact A.mul_mem (intCast_mem A _) (Algebra.subset_adjoin ⟨i, rfl⟩)
  refine ⟨A.toSubring, ?_, ?_⟩
  · unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact hιA x
    · exact A.algebraMap_mem (⟨y.1, y.2⟩ : O)
  · have hg : (g : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have h1 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) = 1 := by
        rw [← map_mul]
        have := congrArg (fun z : O => (z : w.adicCompletion F)) hu
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        have e : (((g : O)) : w.adicCompletion F) = (g : w.adicCompletion F) := by simp
        rw [e] at this
        rw [this, map_one]
      have h2 : Valued.v ((g : w.adicCompletion F)) < 1 := by
        have e : (g : w.adicCompletion F) = ((algebraMap (𝓞 F) F (g : 𝓞 F) : F) : w.adicCompletion F) := by
          rw [map_natCast]
          exact (map_natCast (algebraMap F (w.adicCompletion F)) g).symm
        rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
        exact hgw
      have h3 : Valued.v (u : w.adicCompletion F) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 u.2
      have h4 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right' h3) h2
      rw [h1] at h4
      exact lt_irrefl _ h4
    have hne : Ideal.span {(g : O)} ≠ ⊤ := by
      intro h
      have : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O := by
        rw [Ideal.span_le, Set.singleton_subset_iff]; exact hg
      rw [h] at this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 this)
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A) (Ideal.span {(g : O)}) hne
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_iInf] at hx
    have : (⟨x.1, x.2⟩ : A) ∈ (⨅ i : ℕ, (Ideal.span {(g : O)}) ^ i • (⊤ : Submodule O A)) := by
      rw [Submodule.mem_iInf]
      intro m
      have h1 := hx m
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
      obtain ⟨a, ha⟩ := h1
      have : (⟨x.1, x.2⟩ : A) = ((g : O) ^ m) • (⟨a.1, a.2⟩ : A) := by
        apply Subtype.ext
        have e := congrArg Subtype.val ha
        show x.1 = ((g : O) ^ m) • a.1
        rw [Algebra.smul_def]
        show x.1 = owHom (E := E) w ((g : O) ^ m) * a.1
        rw [map_pow, map_natCast, ← e]
        push_cast
        ring
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m) trivial
    rw [hK] at this
    simpa using this

end sep

section main
open Formalism.HermitianLattices.FiltrationBoundaryCriterion


end main


theorem liftForm {G : Type} [Group G] (Γ U : Subgroup G)
    (hst : ∀ y : G, ∀ γ ∈ Γ, y⁻¹ * γ * y ∈ U → γ = 1)
    {W V : Type} [MulAction U W] [MulAction U V] (p : W → V)
    (hp : ∀ (u : U) (x : W), p (u • x) = u • p x) (f : G → V) (hf : IsForm Γ U f)
    (hs : ∀ g, ∃ x, p x = f g) : ∃ f' : G → W, IsForm Γ U f' ∧ ∀ g, p (f' g) = f g := by
  classical
  let S : G → Set G := fun g => {g' | ∃ γ ∈ Γ, ∃ u : U, g' = γ * g * (u : G)}
  have hSself : ∀ g, g ∈ S g := fun g => ⟨1, Γ.one_mem, 1, by simp⟩
  have hSeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, S (γ * g * (u : G)) = S g := by
    intro g γ hγ u
    ext g'
    constructor
    · rintro ⟨γ', hγ', u', rfl⟩
      exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, u * u', by simp [mul_assoc]⟩
    · rintro ⟨γ', hγ', u', rfl⟩
      exact ⟨γ' * γ⁻¹, Γ.mul_mem hγ' (Γ.inv_mem hγ), u⁻¹ * u', by simp [mul_assoc]⟩
  haveI : Nonempty G := ⟨1⟩
  let rep : G → G := fun g => Classical.epsilon (fun g' => g' ∈ S g)
  have hrep : ∀ g, rep g ∈ S g := fun g => Classical.epsilon_spec (p := fun g' => g' ∈ S g) ⟨g, hSself g⟩
  have hrepeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, rep (γ * g * (u : G)) = rep g := by
    intro g γ hγ u
    show Classical.epsilon (fun g' => g' ∈ S (γ * g * (u : G))) = Classical.epsilon (fun g' => g' ∈ S g)
    rw [hSeq g γ hγ u]
  have hdec : ∀ g, ∃ γ : G, ∃ u : U, γ ∈ Γ ∧ g = γ * rep g * (u : G) := by
    intro g
    obtain ⟨γ, hγ, u, h⟩ := hrep g
    exact ⟨γ⁻¹, u⁻¹, Γ.inv_mem hγ, by rw [h]; simp [mul_assoc]⟩
  choose γf uf hγf hg using hdec
  choose x hx using hs
  refine ⟨fun g => (uf g)⁻¹ • x (rep g), ?_, ?_⟩
  · intro γ hγ u g
    have hr := hrepeq g γ hγ u
    have e1 := hg (γ * g * (u : G))
    rw [hr] at e1
    have e0 := hg g
    set r := rep g
    set γ1 := γf (γ * g * (u : G))
    set u1 := uf (γ * g * (u : G))
    set γ0 := γf g
    set u0 := uf g
    have e2 : γ * (γ0 * r * (u0 : G)) * (u : G) = γ1 * r * (u1 : G) := by rw [← e0]; exact e1
    have e3 : r⁻¹ * (γ1⁻¹ * (γ * γ0)) * r = (u1 : G) * ((u0 : G) * (u : G))⁻¹ := by
      have : γ * γ0 * r = γ1 * r * (u1 : G) * ((u0 : G) * (u : G))⁻¹ := by
        rw [← e2]; simp [mul_assoc]
      calc r⁻¹ * (γ1⁻¹ * (γ * γ0)) * r = r⁻¹ * γ1⁻¹ * (γ * γ0 * r) := by simp [mul_assoc]
        _ = _ := by rw [this]; simp [mul_assoc]
    have e4 : γ1⁻¹ * (γ * γ0) = 1 := by
      apply hst r _ (Γ.mul_mem (Γ.inv_mem (hγf _)) (Γ.mul_mem hγ (hγf _)))
      rw [e3]
      exact U.mul_mem u1.2 (U.inv_mem (U.mul_mem u0.2 u.2))
    have e5 : (u1 : G) = (u0 : G) * (u : G) := by
      rw [e4] at e3
      simp only [mul_one, inv_mul_cancel] at e3
      exact (mul_inv_eq_one.1 e3.symm)
    have e6 : u1 = u0 * u := Subtype.ext e5
    show u1⁻¹ • x (rep (γ * g * (u : G))) = u⁻¹ • u0⁻¹ • x r
    rw [hr, e6, mul_inv_rev, mul_smul]
  · intro g
    show p ((uf g)⁻¹ • x (rep g)) = f g
    rw [hp, hx]
    conv_rhs => rw [hg g]
    exact (hf _ (hγf g) _ _).symm


end S1

section S2
open NumberField IntermediateField

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem sqf_eq (m m' : ℤ) (hm : Squarefree m) (hm' : Squarefree m') (c : ℚ)
    (h : (m : ℚ) = c ^ 2 * m') : m = m' := by
  have e : c * c.den = c.num := Rat.mul_den_eq_num c
  have h1 : (m : ℚ) * (c.den : ℚ) ^ 2 = (c.num : ℚ) ^ 2 * m' := by
    linear_combination (c.den : ℚ) ^ 2 * h + (m' : ℚ) * (c * c.den + c.num) * e
  have h2 : m * (c.den : ℤ) ^ 2 = c.num ^ 2 * m' := by exact_mod_cast h1
  have hcop : IsCoprime c.num (c.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using c.reduced
  have hD : IsUnit (c.den : ℤ) := by
    apply hm'
    have : (c.den : ℤ) * c.den ∣ c.num ^ 2 * m' := ⟨m, by rw [← h2]; ring⟩
    have hc2 : IsCoprime ((c.den : ℤ) * c.den) (c.num ^ 2) := by
      rw [← pow_two]; exact (hcop.symm.pow)
    exact hc2.dvd_of_dvd_mul_left this
  have hN : IsUnit c.num := by
    apply hm
    have : c.num * c.num ∣ m * (c.den : ℤ) ^ 2 := ⟨m', by rw [h2]; ring⟩
    have hc2 : IsCoprime (c.num * c.num) ((c.den : ℤ) ^ 2) := by
      rw [← pow_two]; exact hcop.pow
    exact hc2.dvd_of_dvd_mul_right this
  have hD2 : (c.den : ℤ) ^ 2 = 1 := by
    rcases Int.isUnit_iff.1 hD with h | h <;> rw [h] <;> norm_num
  have hN2 : c.num ^ 2 = 1 := by
    rcases Int.isUnit_iff.1 hN with h | h <;> rw [h] <;> norm_num
  rw [hD2, hN2] at h2
  linarith




section
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem act_zeta (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) (k : ℕ)
    (hk : (k : ZMod (2 ^ (e + 2))) = ((galMap h.1 a b τ).1 : ZMod (2 ^ (e + 2)))) : τ ζ = ζ ^ k := by
  have := h.1.autToPow_spec ℚ τ
  rw [← this]
  have e1 : ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = (k : ZMod (2 ^ (e + 2))) :=
    hk.symm
  rw [e1, ZMod.val_natCast]
  exact (pow_eq_pow_mod k h.1.pow_eq_one).symm


theorem coreQ (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (τ₁ τ₂ τ₃ : Gal(L/ℚ)) (h1 : galMap h.1 a b τ₁ = ((1, -1, 1) : GalL (e + 2)))
    (h2 : galMap h.1 a b τ₂ = ((1, 1, -1) : GalL (e + 2)))
    (h3 : galMap h.1 a b τ₃ = ((u5 (e + 2), 1, 1) : GalL (e + 2)))
    (X y : L) (hX : X ∈ hostE ζ a b) (hy : y ∈ hostE ζ a b) (m m' : ℤ) (hm : Squarefree m)
    (hm' : Squarefree m') (hXm : X ^ 2 = (m : L)) (hym : y ^ 2 = (m' : L))
    (r1 : τ₁ X * y = X * τ₁ y) (r2 : τ₂ X * y = X * τ₂ y) (r3 : τ₃ X * y = X * τ₃ y) : m = m' := by
  obtain ⟨hGal, -, hmul, hbij⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (m' : L) = 0 := by rw [← hym]; ring
    have : m' = 0 := by exact_mod_cast this
    rw [this] at hm'
    exact not_squarefree_zero hm'
  obtain ⟨τ₀, h0⟩ := hbij.2 ((-1, 1, 1) : GalL (e + 2))
  have hfix0 : ∀ x ∈ hostE ζ a b, τ₀ x = x := fun x hx =>
    ((hostFixed e q d hqd L ζ a b h).2 x).1 hx τ₀ h0
  have hrel : ∀ τ : Gal(L/ℚ), τ X * y = X * τ y → τ (X / y) = X / y := by
    intro τ hτ
    have : τ y ≠ 0 := by simpa using hy0
    rw [map_div₀, div_eq_div_iff this hy0, hτ]
  let φ : Gal(L/ℚ) →* GalL (e + 2) := MonoidHom.mk' (galMap h.1 a b) hmul
  let S : Subgroup Gal(L/ℚ) := MulAction.stabilizer Gal(L/ℚ) (X / y)
  have hS : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y → τ ∈ S := fun τ hτ => hτ
  have htop : S.map φ = ⊤ := by
    rw [eq_top_iff, ← (gensModel (e + 2) (by omega)).2.2.2.2, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact ⟨τ₀, hS _ (hrel _ (by rw [hfix0 X hX, hfix0 y hy])), h0⟩
    · exact ⟨τ₃, hS _ (hrel _ r3), h3⟩
    · exact ⟨τ₁, hS _ (hrel _ r1), h1⟩
    · exact ⟨τ₂, hS _ (hrel _ r2), h2⟩
  have hall : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y := by
    intro τ
    have : φ τ ∈ S.map φ := by rw [htop]; trivial
    obtain ⟨τ', hτ', he⟩ := this
    have : τ' = τ := hbij.1 he
    rw [← this]; exact hτ'
  have hbot := (IsGalois.mem_bot_iff_fixed (F := ℚ) (E := L) (X / y)).2 hall
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hbot
  apply sqf_eq m m' hm hm' c
  have hXc : X = algebraMap ℚ L c * y := by rw [hc]; field_simp
  have : ((m : ℚ) : L) = ((c ^ 2 * m' : ℚ) : L) := by
    push_cast
    rw [← hXm, ← hym, hXc]
    simp only [eq_ratCast]
    ring
  exact_mod_cast this

end


open Formalism.HermitianLattices.FiltrationBoundaryCriterion in
theorem hostEOverF : HostEOverF := by
  intro e q d h L _ _ ζ a b hl x
  obtain ⟨_, _, hmul, hbij⟩ := hostGalois e q d h L ζ a b hl
  obtain ⟨c, hc⟩ := hbij.2 (cc e)
  have hreal := (Final.real e q d h L ζ a b hl).2
  have hone : galE e ζ a b 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hcc : c * c = 1 := hbij.1 (by
    rw [hmul, hc, hone]
    simp [cc, c0, Prod.ext_iff])
  have hcc' : ∀ y, c (c y) = y := fun y => by
    have := congrArg (fun s : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b => s y) hcc
    simpa using this
  have hmem : ∀ y : hostE ζ a b, c y = y → y ∈ hostF ζ a b := fun y hy =>
    ((hreal y).1).2 (fun σ hσ => by rw [hbij.1 (hσ.trans hc.symm)]; exact hy)
  have hspec := hostGalSpec e q d h L ζ a b hl c
  have hca : c (aE ζ a b) = - aE ζ a b := by
    apply Subtype.ext
    rw [hspec.1, hc]
    simp [cc, c0, aE]
  have hcb : c (bE ζ a b) = - bE ζ a b := by
    apply Subtype.ext
    rw [hspec.2.1, hc]
    simp [cc, c0, bE]
  have ha0 : aE ζ a b ≠ 0 := by
    intro h0
    have : a = 0 := congrArg Subtype.val h0
    have h2 := hl.2.1
    rw [this] at h2
    have : (q : L) = 0 := by simpa using h2.symm
    exact h.1.ne_zero (by exact_mod_cast this)
  have hb0 : bE ζ a b ≠ 0 := by
    intro h0
    have : b = 0 := congrArg Subtype.val h0
    have h2 := hl.2.2.1
    rw [this] at h2
    have : (d : L) = 0 := by simpa using h2.symm
    exact h.2.1.ne_zero (by exact_mod_cast this)
  have gen : ∀ t : hostE ζ a b, c t = -t → t ≠ 0 →
      ∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * t := by
    intro t ht ht0
    refine ⟨(x + c x) / 2, hmem _ ?_, (x - c x) / (2 * t), hmem _ ?_, ?_⟩
    · simp only [map_div₀, map_add, hcc', map_ofNat]; ring
    · simp only [map_div₀, map_sub, map_mul, hcc', map_ofNat, ht]
      field_simp
      ring
    · field_simp
      ring
  exact ⟨gen _ hcb hb0, gen _ hca ha0⟩

end S2

section S3
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise

section gen
variable {E : Type} [Field E] [NumberField E]

theorem fi_neg_mem {I : FractionalIdeal (𝓞 E)⁰ E} {x : E} (h : x ∈ I) : -x ∈ I := by
  rw [← FractionalIdeal.mem_coe] at h ⊢
  exact neg_mem h

theorem mem_coe_smul (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) (z : E) :
    z ∈ (I : FractionalIdeal (𝓞 E)⁰ E) ↔
      σ z ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨σ • w, Ideal.smul_mem_pointwise_smul σ w I hw, rfl⟩
  · rintro ⟨w, hw, he⟩
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hw
    refine ⟨σ⁻¹ • w, hw, ?_⟩
    show σ⁻¹ (w : E) = z
    have he' : (w : E) = σ z := he
    rw [he']
    exact σ.symm_apply_apply z


theorem quadNorm (K : IntermediateField ℚ E) (hK : Module.finrank ℚ K = 2) (σ : E ≃ₐ[ℚ] E) (β : K)
    (hβ : σ (β : E) ≠ β) (k : K) : ((Algebra.norm ℚ k : ℚ) : E) = (k : E) * σ (k : E) := by
  classical
  let φ0 : E →+* ℂ := Classical.arbitrary _
  let φ : E →ₐ[ℚ] ℂ := φ0.toRatAlgHom
  let τ1 : K →ₐ[ℚ] ℂ := φ.comp K.val
  let τ2 : K →ₐ[ℚ] ℂ := φ.comp ((σ : E →ₐ[ℚ] E).comp K.val)
  have hne : τ1 ≠ τ2 := by
    intro h
    have := DFunLike.congr_fun h β
    exact hβ (φ.injective this).symm
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {τ1, τ2} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, AlgHom.card, hK])).symm
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [huniv, Finset.prod_pair hne] at h1
  apply φ.injective
  rw [map_mul, map_ratCast]
  rw [eq_ratCast] at h1
  exact h1

theorem conjNorm (K : IntermediateField ℚ E) (hK : Module.finrank ℚ K = 2) (σ : E ≃ₐ[ℚ] E) (β : K)
    (hβ : σ (β : E) ≠ β) (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ ⊥) :
    𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))) =
      Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)} := by
  have hnormE : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : E) = ((z : K) : E) * σ ((z : K) : E) := by
    intro z
    rw [← quadNorm K hK σ β hβ (z : K), ← Algebra.coe_norm_int z]
    push_cast; rfl
  have hnorm : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : 𝓞 E) =
      algebraMap (𝓞 K) (𝓞 E) z * σ • algebraMap (𝓞 K) (𝓞 E) z := by
    intro z
    apply RingOfIntegers.ext
    have := hnormE z
    show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_intCast, map_mul]
    exact this
  have hN0 : ((Ideal.absNorm 𝔠 : ℕ) : E) ≠ 0 := by
    have : Ideal.absNorm 𝔠 ≠ 0 := by rwa [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast this
  apply le_antisymm
  · have key : ∀ x ∈ 𝔠, ∀ y ∈ 𝔠, algebraMap (𝓞 K) (𝓞 E) x * σ • algebraMap (𝓞 K) (𝓞 E) y ∈
        Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)} := by
      intro x hx y hy
      obtain ⟨kx, hkx⟩ := Ideal.absNorm_dvd_norm_of_mem hx
      obtain ⟨ky, hky⟩ := Ideal.absNorm_dvd_norm_of_mem hy
      obtain ⟨kxy, hkxy⟩ := Ideal.absNorm_dvd_norm_of_mem (𝔠.add_mem hx hy)
      have ex := hnormE x
      have ey := hnormE y
      have exy := hnormE (x + y)
      rw [hkx] at ex
      rw [hky] at ey
      rw [hkxy] at exy
      push_cast at ex ey exy
      rw [map_add] at exy
      obtain ⟨X, hX⟩ : ∃ X : E, X = ((x : K) : E) := ⟨_, rfl⟩
      obtain ⟨Y, hY⟩ : ∃ Y : E, Y = ((y : K) : E) := ⟨_, rfl⟩
      obtain ⟨X', hX'⟩ : ∃ X' : E, X' = σ ((x : K) : E) := ⟨_, rfl⟩
      obtain ⟨Y', hY'⟩ : ∃ Y' : E, Y' = σ ((y : K) : E) := ⟨_, rfl⟩
      obtain ⟨N, hN⟩ : ∃ N : E, N = ((Ideal.absNorm 𝔠 : ℕ) : E) := ⟨_, rfl⟩
      rw [← hX', ← hX, ← hN] at ex
      rw [← hY', ← hY, ← hN] at ey
      rw [← hX', ← hY', ← hX, ← hY, ← hN] at exy
      rw [← hN] at hN0
      have hkx' : (kx : E) = X * X' / N := by field_simp; linear_combination ex
      have hky' : (ky : E) = Y * Y' / N := by field_simp; linear_combination ey
      have hkxy' : (kxy : E) = (X + Y) * (X' + Y') / N := by field_simp; linear_combination exy
      have hint : IsIntegral ℤ (X * Y' / N) := by
        obtain ⟨T, hT⟩ : ∃ T : ℤ, T = kxy - kx - ky := ⟨_, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M : ℤ, M = kx * ky := ⟨_, rfl⟩
        refine ⟨Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C M, by monicity!, ?_⟩
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        simp only [eq_intCast]
        rw [hT, hM]
        push_cast
        rw [hkx', hky', hkxy']
        field_simp
        ring
      rw [Ideal.mem_span_singleton']
      obtain ⟨w, hw⟩ : ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = X * Y' / N := ⟨⟨_, hint⟩, rfl⟩
      refine ⟨w, ?_⟩
      apply RingOfIntegers.ext
      show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
      rw [map_mul, map_mul, map_natCast, hw]
      show X * Y' / N * ((Ideal.absNorm 𝔠 : ℕ) : E) = ((x : K) : E) * σ ((y : K) : E)
      rw [← hN, ← hX, ← hY']
      field_simp
    rw [Ideal.pointwise_smul_def, Ideal.map_map, Ideal.map, Ideal.map, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact key x hx y hy
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    let J : Ideal ℤ := Ideal.comap (algebraMap ℤ (𝓞 E))
      (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))))
    have hJ : Ideal.relNorm ℤ 𝔠 ≤ J := by
      rw [Ideal.relNorm_apply, Ideal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      refine Ideal.mem_comap.2 ?_
      rw [Algebra.intNorm_eq_norm, eq_intCast, hnorm]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hz)
        (Ideal.smul_mem_pointwise_smul _ _ _ (Ideal.mem_map_of_mem _ hz))
    rw [Ideal.relNorm_int] at hJ
    have := hJ (Ideal.mem_span_singleton_self _)
    have h2 : algebraMap ℤ (𝓞 E) ((Ideal.absNorm 𝔠 : ℕ) : ℤ) ∈
      (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E)))) := this
    simpa using h2

end gen

section main
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.FiltrationBoundaryCriterion

theorem algG {G : Type*} [CommGroupWithZero G] (cB cB' s cC cC' : G) (h1 : cB' ≠ 0) (h2 : cC ≠ 0) :
    (cB * cB' * s)⁻¹ * (cC' * cB'⁻¹)⁻¹ = (cC * cC' * s)⁻¹ * (cC * cB⁻¹) := by
  simp only [mul_inv, inv_inv]
  calc cB⁻¹ * cB'⁻¹ * s⁻¹ * (cC'⁻¹ * cB') = (cB'⁻¹ * cB') * (cB⁻¹ * s⁻¹ * cC'⁻¹) := by ac_rfl
    _ = (cC⁻¹ * cC) * (cB⁻¹ * s⁻¹ * cC'⁻¹) := by rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
    _ = _ := by ac_rfl

theorem signs (e q d : ℕ) (hH : HostHyp q d)
    (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ = cc e) (N : ℕ)
    (ξ : hostE ζ a b) (hξ : ξ * ((N : hostE ζ a b) * bE ζ a b) = -1) :
    σ ξ = -ξ ∧ (∀ φ ∈ cmType ζ a b d, 0 < (φ ξ).im) := by
  constructor
  · have hb : σ (bE ζ a b) = - bE ζ a b := by
      have := (hostGalSpec e q d hH.toHypOdd L ζ a b h σ).2.1
      rw [hσ] at this
      apply Subtype.ext
      rw [this]
      simp [cc, c0, bE]
    have h1 := congrArg σ hξ
    simp only [map_mul, map_natCast, hb, map_neg, map_one] at h1
    have hne : ((N : hostE ζ a b) * bE ζ a b) ≠ 0 := by
      intro h0; rw [h0] at hξ; simp at hξ
    have : (σ ξ + ξ) * ((N : hostE ζ a b) * bE ζ a b) = 0 := by linear_combination hξ - h1
    rcases mul_eq_zero.1 this with h2 | h2
    · linear_combination h2
    · exact absurd h2 hne
  · intro φ hφ
    have hb : φ (bE ζ a b) = Complex.I * (Real.sqrt d : ℂ) := hφ
    have h1 := congrArg φ hξ
    simp only [map_mul, map_natCast, hb, map_neg, map_one] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    have hr : 0 ≤ (N : ℝ) * Real.sqrt d := by positivity
    by_contra hneg
    have hneg' : (φ ξ).im ≤ 0 := not_lt.1 hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg' hr
    linarith


end main

end S3

end PfB


end Formalism.HermitianLattices.StabilizerLevels
