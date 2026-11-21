import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairSplitSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarDvrOfIsSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureOfIsArtinianRing

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut.TorsorField

theorem exists_point_pi {K G A Ω : Type} [CommRing K] [Fintype G] [DecidableEq G] [CommRing A]
    [Algebra K A] [Field Ω] [Algebra K Ω] (z : (G → A) →ₐ[K] Ω) :
    ∃ g : G, ∀ f : G → A, z f = z (fun _ => f g) := by
  have hs : ∑ g, (Pi.single g (1 : A) : G → A) = 1 := by
    simpa using Finset.univ_sum_single (1 : G → A)
  have hsum : ∑ g, z (Pi.single g 1) = 1 := by rw [← map_sum, hs, map_one]
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun g => z (Pi.single g 1)) (by rw [hsum]; exact one_ne_zero)
  have hidem : z (Pi.single g 1) = 1 := by
    have h2 : z (Pi.single g 1) * z (Pi.single g 1) = z (Pi.single g 1) * 1 := by
      rw [← map_mul, mul_one]; congr 1; funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
    exact mul_left_cancel₀ hg h2
  refine ⟨g, fun f => ?_⟩
  have hf : f * Pi.single g 1 = (fun _ => f g) * Pi.single g 1 := by
    funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
  calc z f = z f * z (Pi.single g 1) := by rw [hidem, mul_one]
    _ = z (fun _ => f g) * z (Pi.single g 1) := by rw [← map_mul, ← map_mul, hf]
    _ = z (fun _ => f g) := by rw [hidem, mul_one]

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

abbrev galMap (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) :
    M ⊗[K] M →ₐ[K] (Multiplicative (ZMod q) → M) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun _ => AlgHom.id K M))
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun g => (act g).toAlgHom))

theorem galMap_tmul (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (a b : M) :
    galMap act (a ⊗ₜ b) = fun g => a * act g b := by
  funext g; simp [galMap, Algebra.TensorProduct.productMap_apply_tmul]

theorem exists_eq_comp [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x y : M →ₐ[K] Ω) : ∃ g, y = x.comp (act g).toAlgHom := by
  classical
  let Φ := AlgEquiv.ofBijective (galMap act) hbij
  let z := (Algebra.TensorProduct.productMap x y).comp Φ.symm.toAlgHom
  obtain ⟨g, hg⟩ := exists_point_pi z
  have key : ∀ a b : M, x a * y b = z (fun _ => a * act g b) := by
    intro a b
    have hΦ : Φ.symm (galMap act (a ⊗ₜ b)) = a ⊗ₜ b := by
      show Φ.symm (Φ (a ⊗ₜ b)) = _
      exact Φ.symm_apply_apply _
    have h1 : z (galMap act (a ⊗ₜ b)) = x a * y b := by
      show Algebra.TensorProduct.productMap x y (Φ.symm (galMap act (a ⊗ₜ b))) = _
      rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul]
    rw [← h1, hg, galMap_tmul]
  have hx : ∀ a, x a = z (fun _ => a) := fun a => by simpa using key a 1
  refine ⟨g, AlgHom.ext fun b => ?_⟩
  have h := key 1 b
  rw [map_one, one_mul, one_mul] at h
  rw [h, ← hx]; rfl

theorem eq_of_comp_eq [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x : M →ₐ[K] Ω) {g g' : Multiplicative (ZMod q)}
    (h : x.comp (act g).toAlgHom = x.comp (act g').toAlgHom) : g = g' := by
  classical
  by_contra hne
  obtain ⟨w, hw⟩ := hbij.2 (Pi.single g 1)
  have hZ : ∀ k, Algebra.TensorProduct.productMap x (x.comp (act k).toAlgHom) =
      (x.comp (Pi.evalAlgHom K (fun _ => M) k)).comp (galMap act) := by
    intro k; apply Algebra.TensorProduct.ext'; intro a b
    rw [AlgHom.comp_apply, galMap_tmul, Algebra.TensorProduct.productMap_apply_tmul]
    simp
  have e1 := congrArg (fun F => F w) (hZ g)
  have e2 := congrArg (fun F => F w) (hZ g')
  simp only [AlgHom.comp_apply, hw, Pi.evalAlgHom_apply] at e1 e2
  rw [h] at e1
  rw [Pi.single_eq_same] at e1
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at e2
  have := e1.symm.trans e2
  simp at this

end GlobalTheory.KeyOriginCut.TorsorField

namespace GlobalTheory.KeyOriginCut.TorsorField

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

theorem factor_isGalois_dvd [NeZero q] {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M))
    (hbij : Function.Bijective (galMap act)) (π : M →ₐ[K] L) (hπ : Function.Surjective π) :
    IsGalois K L ∧ Module.finrank K L ∣ q := by
  classical
  let Ω := AlgebraicClosure K
  let σ0 : L →ₐ[K] Ω := IsAlgClosed.lift
  have hσ0inj : Function.Injective σ0 := σ0.toRingHom.injective
  let P : Multiplicative (ZMod q) → Prop := fun g => ∀ a, π a = 0 → π (act g a) = 0
  have hPmul : ∀ g h, P g → P h → P (g * h) := by
    intro g h hg hh a ha; rw [map_mul, AlgEquiv.mul_apply]; exact hg _ (hh a ha)
  have hPone : P 1 := by intro a ha; rw [map_one, AlgEquiv.one_apply]; exact ha
  have hPpow : ∀ g (n : ℕ), P g → P (g ^ n) := by
    intro g n hg; induction n with
    | zero => rw [pow_zero]; exact hPone
    | succ n ih => rw [pow_succ]; exact hPmul _ _ ih hg
  let H : Subgroup (Multiplicative (ZMod q)) :=
    { carrier := {g | P g}
      mul_mem' := fun {g h} hg hh => hPmul g h hg hh
      one_mem' := hPone
      inv_mem' := fun {g} hg => by
        show P g⁻¹
        have hc : g ^ (Fintype.card (Multiplicative (ZMod q)) - 1) * g = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos, pow_card_eq_one]
        rw [← eq_inv_of_mul_eq_one_left hc]
        exact hPpow g _ hg }
  have hτ : ∀ g, P g → ∃ τ : L →ₐ[K] L, τ.comp π = π.comp (act g).toAlgHom := by
    intro g hg
    let E := Ideal.quotientKerAlgEquivOfSurjective hπ
    let f := Ideal.Quotient.liftₐ (RingHom.ker π) (π.comp (act g).toAlgHom)
      (fun a ha => hg a (RingHom.mem_ker.1 ha))
    refine ⟨f.comp E.symm.toAlgHom, AlgHom.ext fun a => ?_⟩
    have hE : E.symm (π a) = Ideal.Quotient.mk _ a := E.symm_apply_eq.2 rfl
    show f (E.symm (π a)) = π (act g a)
    rw [hE]; rfl
  choose! τ hτc using hτ
  have hΨ : ∀ g, P g → (σ0.comp (τ g)).comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro g hg; rw [AlgHom.comp_assoc, hτc g hg, ← AlgHom.comp_assoc]
  have hB : ∀ σ : L →ₐ[K] Ω, ∃ g, P g ∧ σ.comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro σ
    obtain ⟨g, hg⟩ := exists_eq_comp act hbij (σ0.comp π) (σ.comp π)
    refine ⟨g, fun a ha => hσ0inj ?_, hg⟩
    have h := congrArg (fun F => F a) hg
    simp only [AlgHom.comp_apply] at h
    rw [map_zero]; exact h.symm.trans (by rw [ha, map_zero])
  have hcancel : ∀ σ σ' : L →ₐ[K] Ω, σ.comp π = σ'.comp π → σ = σ' := by
    intro σ σ' h; ext l; obtain ⟨a, rfl⟩ := hπ l
    exact congrArg (fun F => F a) h

  let Ψ : H → (L →ₐ[K] Ω) := fun g => σ0.comp (τ g)
  have hΨbij : Function.Bijective Ψ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun σ => ?_⟩
    · have h2 : (σ0.comp π).comp (act g.1).toAlgHom = (σ0.comp π).comp (act g'.1).toAlgHom := by
        rw [← hΨ _ g.2, ← hΨ _ g'.2]; exact congrArg (fun F => F.comp π) h
      exact eq_of_comp_eq act hbij _ h2
    · obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨⟨g, hg⟩, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
  have hcardΩ : Nat.card (L →ₐ[K] Ω) = Module.finrank K L := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  have hcardH : Nat.card H = Module.finrank K L := (Nat.card_eq_of_bijective Ψ hΨbij).trans hcardΩ
  refine ⟨?_, ?_⟩
  ·
    have hsurj : Function.Surjective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro σ
      obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨τ g, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
    have hinj : Function.Injective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro a b h; ext l; exact hσ0inj (congrArg (fun F => F l) h)
    have hLL : Nat.card (L →ₐ[K] L) = Module.finrank K L :=
      (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).trans hcardΩ
    apply IsGalois.of_card_aut_eq_finrank
    rw [← hLL]
    exact Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).toEquiv
  · rw [← hcardH]
    have := Subgroup.card_subgroup_dvd_card H
    simpa [Nat.card_eq_fintype_card] using this

end GlobalTheory.KeyOriginCut.TorsorField

open GlobalTheory.KeyOriginCut.TorsorField in

theorem GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois :
    ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  intro K M _ _ _ q act hq htor
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.Etale K M := GlobalTheory.KeyOriginCut.etale_of_isZTorsor K M q act htor
  obtain ⟨I, hI, L, hF, hA, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K M).1 inferInstance
  have hbij : Function.Bijective (galMap act) := htor.2.2.2
  have key : ∀ i, IsGalois K (L i) ∧ Module.finrank K (L i) ∣ q := by
    intro i
    haveI := (hL i).1
    haveI := (hL i).2
    exact factor_isGalois_dvd act hbij ((Pi.evalAlgHom K L i).comp e.toAlgHom)
      ((Function.surjective_eval i).comp e.surjective)
  exact ⟨I, Fintype.ofFinite I, L, hF, hA, fun i => (hL i).1, fun i => (key i).1,
    fun i => (key i).2, ⟨e⟩⟩
end
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_field_eq_prod_galois : ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (exact GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (intros; apply GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.RamGalDVR

theorem isSeparable_of_natCast_finrank_ne_zero' {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  have hdvd := minpoly.degree_dvd hint
  show (minpoly F x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro hd
  set n := (minpoly F x).natDegree with hn
  have hpos : 0 < n := minpoly.natDegree_pos hint
  have hc := congrArg (fun p : Polynomial F => p.coeff (n - 1)) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
  rw [Nat.sub_add_cancel hpos] at hc
  have hlead : (minpoly F x).coeff n = 1 := minpoly.monic hint
  rw [hlead, one_mul] at hc
  have hn0 : (n : F) = 0 := by
    have : ((n - 1 : ℕ) : F) + 1 = ((n - 1 + 1 : ℕ) : F) := by push_cast; ring
    rw [this, Nat.sub_add_cancel hpos] at hc
    exact hc
  obtain ⟨c, hc'⟩ := hdvd
  exact h (by rw [hc', Nat.cast_mul, hn0, zero_mul])

theorem isSeparable_of_isField {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    [Module.Finite F E] (hF : IsField F) (hE : IsField E)
    (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  letI := hF.toField
  letI := hE.toField
  exact @isSeparable_of_natCast_finrank_ne_zero' F E _ _ ‹Algebra F E› ‹Module.Finite F E› h

theorem ramGal : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ q _ hq hdeg
  set B := integralClosure S L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Module.Finite S B := IsIntegralClosure.finite S K L B
  have : IsGaloisGroup (L ≃ₐ[K] L) S B := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have : FaithfulSMul S B :=
    (faithfulSMul_iff_algebraMap_injective S _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat S B :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal S) B (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at hfund
  have hef : Ideal.ramificationIdxIn (maximalIdeal S) B * Ideal.inertiaDegIn (maximalIdeal S) B ∣ q :=
    (Dvd.intro_left _ hfund).trans hdeg
  have hlies : ∀ P : Ideal B, P.IsMaximal → P.LiesOver (maximalIdeal S) := by
    intro P hP
    refine ⟨?_⟩
    have : (P.under S).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  refine ⟨fun P hP => ?_, fun P hP _ => ?_⟩
  · have := hlies P hP
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal S) P (L ≃ₐ[K] L)]
    exact (Dvd.intro _ rfl).trans hef
  · have := hP
    have : (maximalIdeal S).IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
    have hf : Module.finrank (S ⧸ maximalIdeal S) (B ⧸ P) ∣ q := by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal S) P,
        ← Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal S) P (L ≃ₐ[K] L)]
      exact (Dvd.intro_left _ rfl).trans hef
    have : Module.Finite S (B ⧸ P) := inferInstance
    have : Module.Finite (S ⧸ maximalIdeal S) (B ⧸ P) :=
      Module.Finite.of_restrictScalars_finite S _ _
    refine isSeparable_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hP) ?_
    obtain ⟨c, hc⟩ := hf
    intro h0
    have hu : IsUnit ((q : S) : S ⧸ maximalIdeal S) := hq.map (Ideal.Quotient.mk _)
    rw [map_natCast, hc, Nat.cast_mul, h0, zero_mul] at hu
    exact not_isUnit_zero hu

end GlobalTheory.RamGalDVR
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationIdx_dvd_of_galois_degree_dvd_unit_dvr : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  first | (exact @GlobalTheory.RamGalDVR.ramGal) | (exact GlobalTheory.RamGalDVR.ramGal) | (intros; apply GlobalTheory.RamGalDVR.ramGal  <;> assumption)
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abhyankar_dvr_of_isSeparable_alt : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale D (integralClosure D (TensorProduct S D L)) := by
  first | (exact @GlobalTheory.abhyankar_dvr_of_isSeparable) | (exact GlobalTheory.abhyankar_dvr_of_isSeparable) | (intros; apply GlobalTheory.abhyankar_dvr_of_isSeparable  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem exists_one_tmul_eq_of_isIntegral_smooth_fractionField
    (R K B : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (x : K ⊗[R] B) (hx : IsIntegral R x) : ∃ b : B, x = (1 : K) ⊗ₜ[R] b := by
  let e := Algebra.TensorProduct.comm R K B
  have h1 : IsIntegral R (e x) := hx.map e.toAlgHom
  have h2 : IsIntegral B (e x) := h1.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := B) (B := K)).2 ⟨e x, h2⟩
  have hy' : (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = e x := congrArg Subtype.val hy
  have key : ∀ y : B ⊗[R] integralClosure R K, ∃ b : B,
      (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = b ⊗ₜ[R] (1 : K) := by
    intro y
    induction y with
    | zero => exact ⟨0, by simp⟩
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, e.injective ?_⟩
  rw [← hy', hb]
  simp [e]

theorem etale_integralClosure_tensor_of_etale_of_isIntegral :
    ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  intro S₁ K₁ T _ _ _ _ _ _ _ _ hE hI
  let i : T →ₐ[S₁] K₁ ⊗[S₁] T := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S₁ K₁)
  have hint : ∀ t : T, i t ∈ integralClosure S₁ (K₁ ⊗[S₁] T) := fun t =>
    (Algebra.IsIntegral.isIntegral (R := S₁) t).map i
  let φ : T →ₐ[S₁] integralClosure S₁ (K₁ ⊗[S₁] T) := i.codRestrict _ hint
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := exists_one_tmul_eq_of_isIntegral_smooth_fractionField S₁ K₁ T x hx
      exact ⟨b, Subtype.ext hb.symm⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ)

end GlobalTheory
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_tensor : ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  first | (exact @GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (exact GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (intros; apply GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing : ∀ (S K L F : Type) [CommRing S] [Field K] [Algebra S K] [IsFractionRing S K] [CommRing L]
    [Algebra K L] [Algebra S L] [IsScalarTower S K L] [CommRing F] [Algebra K F] [Algebra S F]
    [IsScalarTower S K F], Nonempty (F ⊗[S] L ≃ₐ[F] F ⊗[K] L) := by
  intro S K L F _ _ _ _ _ _ _ _ _ _ _ _
  have hb : IsBaseChange K (LinearMap.id : L →ₗ[S] L) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mp
      (isLocalizedModule_id (nonZeroDivisors S) L K)
  let g : K ⊗[S] L →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) (AlgHom.id S L) (fun _ _ => Commute.all _ _)
  have hg : (g : K ⊗[S] L → L) = hb.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp [g, IsBaseChange.equiv_tmul, Algebra.smul_def]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let e0 : K ⊗[S] L ≃ₐ[K] L := AlgEquiv.ofBijective g (by rw [hg]; exact hb.equiv.bijective)
  exact ⟨(Algebra.TensorProduct.cancelBaseChange S K F F L).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl e0)⟩

theorem GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem : ∀ (D B F : Type) [CommRing D] [CommRing B] [Algebra D B] [CommRing F] [Algebra D F]
    (N : Subalgebra D B) (M : Submonoid D), (∀ m ∈ M, IsUnit (algebraMap D F m)) →
    (∀ b : B, ∃ m ∈ M, m • b ∈ N) →
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) := by
  intro D B F _ _ _ _ _ N M hM hN
  let Dm := Localization M
  have hM' : ∀ y : M, IsUnit (algebraMap D F y) := fun y => hM y y.2
  letI : Algebra Dm F := (IsLocalization.lift (M := M) (S := Dm) (g := algebraMap D F) hM').toAlgebra
  haveI : IsScalarTower D Dm F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq (M := M) (S := Dm) hM' x).symm)
  let ι : Dm ⊗[D] N →ₐ[Dm] Dm ⊗[D] B := Algebra.TensorProduct.map (AlgHom.id Dm Dm) N.val
  have hι : Function.Bijective ι := by
    constructor
    · have := Module.Flat.lTensor_preserves_injective_linearMap (M := Dm) N.val.toLinearMap
        Subtype.val_injective
      exact this
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul a b =>
        obtain ⟨m, hm, hmb⟩ := hN b
        let u := (IsLocalization.map_units Dm (⟨m, hm⟩ : M)).unit
        refine ⟨(a * ↑u⁻¹) ⊗ₜ[D] (⟨m • b, hmb⟩ : N), ?_⟩
        simp only [ι, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
        rw [← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        have hu : (u : Dm) = algebraMap D Dm m := rfl
        rw [← hu, mul_left_comm, Units.mul_inv, mul_one]
      | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
  let eι : Dm ⊗[D] N ≃ₐ[Dm] Dm ⊗[D] B := AlgEquiv.ofBijective ι hι
  let E : F ⊗[D] N ≃ₐ[F] F ⊗[D] B :=
    (Algebra.TensorProduct.cancelBaseChange D Dm F F N).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl eι).trans
        (Algebra.TensorProduct.cancelBaseChange D Dm F F B))
  have hE : ⇑(Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) = ⇑E := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f n =>
      simp [E, eι, ι, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hE]
  exact E.bijective

theorem GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L] [Algebra.IsAlgebraic K L]
    [CommRing D] [Algebra S D], ∀ b : D ⊗[S] L,
    ∃ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), m • b ∈ integralClosure D (D ⊗[S] L) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ b
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | tmul d l =>
    obtain ⟨s, hs0, hint⟩ := IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff S K L).mpr (Algebra.IsAlgebraic.isAlgebraic l))
    refine ⟨algebraMap S D s, ⟨s, mem_nonZeroDivisors_of_ne_zero hs0, rfl⟩, ?_⟩
    have h1 : algebraMap S D s • (d ⊗ₜ[S] l) = algebraMap D (D ⊗[S] L) d * ((1 : D) ⊗ₜ[S] (s • l)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        algebraMap_smul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.tmul_smul]
    rw [h1]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ d) ?_
    exact (hint.map (Algebra.TensorProduct.includeRight : L →ₐ[S] D ⊗[S] L)).tower_top
  | add x y hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 * m2, mul_mem hm1 hm2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Subalgebra.smul_mem _ h1 _
    · rw [mul_smul]; exact Subalgebra.smul_mem _ h2 _

theorem GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  intro S S₁ K K₁ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy hram hsep
  let f : S[X] := X ^ q - C π
  let D := AdjoinRoot f
  have hD : Algebra.Etale D (integralClosure D (D ⊗[S] L)) :=
    GlobalTheory.T.abhyankar_dvr_of_isSeparable_alt S K L π q D ⟨AlgEquiv.refl⟩ hπ hqu hram hsep
  let φ : D →ₐ[S] S₁ := AdjoinRoot.liftAlgHom f (Algebra.ofId S S₁) y (by simp [f, hy])
  letI : Algebra D S₁ := φ.toRingHom.toAlgebra
  letI : Algebra D K₁ := ((algebraMap S₁ K₁).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower D S₁ K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower S D S₁ := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  haveI : IsScalarTower S D K₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply S S₁ K₁, IsScalarTower.algebraMap_apply S D S₁]; rfl)
  let N := integralClosure D (D ⊗[S] L)
  let T := S₁ ⊗[D] N
  haveI : Algebra.Etale S₁ T := Algebra.Etale.baseChange D N S₁
  haveI : Algebra.IsIntegral S₁ T := Algebra.IsIntegral.tensorProduct D S₁ N
  haveI hT := GlobalTheory.T.etale_integralClosure_tensor S₁ K₁ T inferInstance inferInstance
  have hunit : ∀ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), IsUnit (algebraMap D K₁ m) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S S₁ K₁]
    refine IsUnit.mk0 _ ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective S₁ K₁), map_eq_zero_iff _ hinj]
    exact nonZeroDivisors.ne_zero hs
  let e1 : K₁ ⊗[S₁] T ≃ₐ[K₁] K₁ ⊗[D] N := Algebra.TensorProduct.cancelBaseChange D S₁ K₁ K₁ N
  let e2 : K₁ ⊗[D] N ≃ₐ[K₁] K₁ ⊗[D] (D ⊗[S] L) :=
    AlgEquiv.ofBijective _ (GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem D (D ⊗[S] L) K₁ N _ hunit (GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor S K L D))
  let e3 : K₁ ⊗[D] (D ⊗[S] L) ≃ₐ[K₁] K₁ ⊗[S] L := Algebra.TensorProduct.cancelBaseChange S D K₁ K₁ L
  obtain ⟨e4⟩ := GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing S K L K₁
  let e : K₁ ⊗[S₁] T ≃ₐ[S₁] K₁ ⊗[K] L := (((e1.trans e2).trans e3).trans e4).restrictScalars S₁
  exact Algebra.Etale.of_equiv e.mapIntegralClosure
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  first | (exact @GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (exact GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (intros; apply GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.PiClosure

noncomputable def integralClosurePiEquiv (R : Type) [CommRing R] (ι : Type) [Finite ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)] :
    integralClosure R (∀ i, E i) ≃ₐ[R] ∀ i, integralClosure R (E i) :=
  AlgEquiv.ofBijective
    (AlgHom.pi fun i =>
      ((Pi.evalAlgHom R E i).comp (integralClosure R (∀ i, E i)).val).codRestrict
        (integralClosure R (E i)) fun x => x.2.map (Pi.evalAlgHom R E i))
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        funext i
        exact congrArg Subtype.val (congrFun hxy i)
      · intro l
        refine ⟨⟨fun i => (l i).1,
          GlobalTheory.PurityProd.isIntegral_of_forall_apply (fun i => (l i).1) fun i => (l i).2⟩, ?_⟩
        funext i
        rfl)

theorem etale_integralClosure_pi : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  intro R _ ι _ E _ _ h
  haveI : Algebra.Etale R (∀ i, integralClosure R (E i)) := inferInstance
  exact Algebra.Etale.of_equiv (integralClosurePiEquiv R ι E).symm

end GlobalTheory.PiClosure
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_pi_of_etale : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  first | (exact @GlobalTheory.PiClosure.etale_integralClosure_pi) | (exact GlobalTheory.PiClosure.etale_integralClosure_pi) | (intros; apply GlobalTheory.PiClosure.etale_integralClosure_pi  <;> assumption)
end

section
namespace GlobalTheory.RingHomTensorExtensionality

theorem ringHom_ext_tensor {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] {g h : TensorProduct R A B →+* C}
    (ha : ∀ a : A, g (a ⊗ₜ[R] (1 : B)) = h (a ⊗ₜ[R] (1 : B)))
    (hb : ∀ b : B, g ((1 : A) ⊗ₜ[R] b) = h ((1 : A) ⊗ₜ[R] b)) : g = h := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    have e : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, ha, hb]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.RingHomTensorExtensionality
end

section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginTransport

section Lift

variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
  [Algebra R B]

def tensorLift (u : A →+* C) (v : B →+* C) (h : u.comp (algebraMap R A) = v.comp (algebraMap R B)) :
    A ⊗[R] B →+* C :=
  letI : Algebra R C := (v.comp (algebraMap R B)).toAlgebra
  (Algebra.TensorProduct.productMap
    (⟨u, fun r => by
        show u (algebraMap R A r) = v (algebraMap R B r)
        exact congrArg (fun w : R →+* C => w r) h⟩ : A →ₐ[R] C)
    (⟨v, fun _ => rfl⟩ : B →ₐ[R] C)).toRingHom

theorem tensorLift_tmul (u : A →+* C) (v : B →+* C)
    (h : u.comp (algebraMap R A) = v.comp (algebraMap R B)) (a : A) (b : B) :
    tensorLift u v h (a ⊗ₜ[R] b) = u a * v b := by
  simp [tensorLift, Algebra.TensorProduct.productMap_apply_tmul]

theorem ringHom_ext {g h : A ⊗[R] B →+* C} (h1 : ∀ a : A, g (a ⊗ₜ[R] (1 : B)) = h (a ⊗ₜ[R] (1 : B)))
    (h2 : ∀ b : B, g ((1 : A) ⊗ₜ[R] b) = h ((1 : A) ⊗ₜ[R] b)) : g = h := by
  first
  | exact @_root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor
  | exact _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor
  | (apply _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RingHomTensorExtensionality.ringHom_ext_tensor ..)

theorem algebraMap_tmul_one (r : R) :
    (algebraMap R A r) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end Lift

theorem exists_dvd_pow {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {s x : S}
    (hs : s ≠ 0) (hx0 : x ≠ 0) (hx : ¬ IsUnit x) : ∃ n : ℕ, s ∣ x ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs hϖ
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      exact absurd (hb.symm.isUnit (by simp)) hx
    · exact h
  refine ⟨a, ha.dvd.trans ?_⟩
  calc ϖ ^ a ∣ (ϖ ^ b) ^ a := by
        rw [← pow_mul]; exact pow_dvd_pow _ (Nat.le_mul_of_pos_left a hb1)
    _ ∣ x ^ a := pow_dvd_pow_of_dvd hb.symm.dvd a

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

section FirstIso

variable {R₁ B₁ S₁ K₁ B DA : Type} [CommRing R₁] [CommRing B₁] [CommRing S₁] [CommRing K₁]
  [CommRing B] [CommRing DA] [Algebra R₁ B₁] [Algebra R₁ S₁] [Algebra S₁ K₁] [Algebra B DA]
  [Algebra B K₁] (β : B →+* B₁)

abbrev ov (b : B₁) : Over β := b

theorem algebraMap_bc (b : B₁) :
    algebraMap B₁ (BC β DA) b = ov β b ⊗ₜ[B] (1 : DA) := rfl

theorem tmul_one_bc (b : B) :
    ov β (β b) ⊗ₜ[B] (1 : DA) = (1 : Over β) ⊗ₜ[B] algebraMap B DA b :=
  algebraMap_tmul_one (A := Over β) b

def vE (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β) : BC β DA →+* K₁ ⊗[B] DA :=
  tensorLift (R := B) (A := Over β) (Algebra.TensorProduct.includeLeftRingHom.comp ι : B₁ →+* K₁ ⊗[B] DA)
    (Algebra.TensorProduct.includeRight : DA →ₐ[B] K₁ ⊗[B] DA).toRingHom (by
      apply RingHom.ext; intro b
      show ι (β b) ⊗ₜ[B] (1 : DA) = (1 : K₁) ⊗ₜ[B] algebraMap B DA b
      rw [← RingHom.comp_apply ι β, ← hBK]
      exact algebraMap_tmul_one b)

theorem vE_tmul (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β) (b : B₁) (d : DA) :
    vE β ι hBK (ov β b ⊗ₜ[B] d) = ι b ⊗ₜ[B] d := by
  unfold vE
  refine (tensorLift_tmul (R := B) (A := Over β) _ _ _ b d).trans ?_
  show (ι b ⊗ₜ[B] (1 : DA)) * ((1 : K₁) ⊗ₜ[B] d) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

def fwd₁ [Algebra R₁ (BC β DA)] (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β)
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁)) :
    S₁ ⊗[R₁] BC β DA →+* K₁ ⊗[B] DA :=
  tensorLift (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap S₁ K₁)) (vE β ι hBK) (by
    apply RingHom.ext; intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, hD]
    simp only [RingHom.comp_apply]
    rw [algebraMap_bc, vE_tmul, ← RingHom.comp_apply ι, hι, RingHom.comp_apply]
    rfl)

theorem fwd₁_tmul [Algebra R₁ (BC β DA)] (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β)
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁)) (s : S₁) (z : BC β DA) :
    fwd₁ β ι hBK hD hι (s ⊗ₜ[R₁] z) = (algebraMap S₁ K₁ s ⊗ₜ[B] (1 : DA)) * vE β ι hBK z := by
  unfold fwd₁
  exact tensorLift_tmul _ _ _ s z

def uT [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
    (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA))) :
    K₁ →+* S₁ ⊗[R₁] BC β DA :=
  IsLocalization.lift (M := nonZeroDivisors S₁) (g := Algebra.TensorProduct.includeLeftRingHom)
    (fun s => hunit s.1 s.2)

theorem uT_algebraMap [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
    (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA))) (s : S₁) :
    uT (K₁ := K₁) β hunit (algebraMap S₁ K₁ s) = s ⊗ₜ[R₁] (1 : BC β DA) := by
  unfold uT
  exact IsLocalization.lift_eq _ _

theorem uT_comp_ι [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
    (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA))) (ι : B₁ →+* K₁)
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁))
    (N : Submonoid R₁) [IsLocalization N B₁] :
    (uT β hunit).comp ι =
      (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA).toRingHom.comp
        (algebraMap B₁ (BC β DA)) := by
  apply IsLocalization.ringHom_ext N
  apply RingHom.ext; intro r
  simp only [RingHom.comp_apply]
  rw [← RingHom.comp_apply ι, hι, RingHom.comp_apply, uT_algebraMap, ← RingHom.comp_apply _ (algebraMap R₁ B₁), ← hD]
  exact algebraMap_tmul_one r

end FirstIso

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

section FirstIso2

variable {R₁ B₁ S₁ K₁ B DA : Type} [CommRing R₁] [CommRing B₁] [CommRing S₁] [CommRing K₁]
  [CommRing B] [CommRing DA] [Algebra R₁ B₁] [Algebra R₁ S₁] [Algebra S₁ K₁] [Algebra B DA]
  [Algebra B K₁] (β : B →+* B₁) [Algebra R₁ (BC β DA)] [IsFractionRing S₁ K₁]
  (ι : B₁ →+* K₁) (hBK : algebraMap B K₁ = ι.comp β)
  (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
  (hι : ι.comp (algebraMap R₁ B₁) = (algebraMap S₁ K₁).comp (algebraMap R₁ S₁))
  (hunit : ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA)))
  (N : Submonoid R₁) [IsLocalization N B₁]

def bwd₁ : K₁ ⊗[B] DA →+* S₁ ⊗[R₁] BC β DA :=
  tensorLift (R := B) (uT β hunit)
    ((Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA).toRingHom.comp
      (Algebra.TensorProduct.includeRight : DA →ₐ[B] BC β DA).toRingHom) (by
    apply RingHom.ext; intro b
    rw [RingHom.comp_apply, hBK, RingHom.comp_apply, ← RingHom.comp_apply (uT β hunit) ι,
      uT_comp_ι β hunit ι hD hι N]
    show (1 : S₁) ⊗ₜ[R₁] (algebraMap B₁ (BC β DA) (β b)) =
      (1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] algebraMap B DA b)
    rw [algebraMap_bc, tmul_one_bc])

omit [IsFractionRing S₁ K₁] [Algebra S₁ K₁] [Algebra B K₁] in
theorem one_tmul_one_bc : ((1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] (1 : DA)) : S₁ ⊗[R₁] BC β DA) = 1 := by
  rw [← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def]

theorem bwd₁_tmul (k : K₁) (d : DA) :
    bwd₁ β ι hBK hD hι hunit N (k ⊗ₜ[B] d) =
      uT β hunit k * ((1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] d)) := by
  unfold bwd₁
  exact tensorLift_tmul _ _ _ k d

theorem fwd₁_comp_uT :
    (fwd₁ β ι hBK hD hι).comp (uT β hunit) = Algebra.TensorProduct.includeLeftRingHom := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors S₁)
  apply RingHom.ext; intro s
  rw [RingHom.comp_apply, RingHom.comp_apply, uT_algebraMap, fwd₁_tmul, map_one, mul_one]
  rfl

theorem bwd₁_comp_vE :
    (bwd₁ β ι hBK hD hι hunit N).comp (vE β ι hBK) =
      (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA).toRingHom := by
  apply ringHom_ext (A := Over β)
  · intro (a : B₁)
    change (bwd₁ β ι hBK hD hι hunit N) ((vE β ι hBK) (ov β a ⊗ₜ[B] (1 : DA))) = _
    rw [vE_tmul, bwd₁_tmul, ← RingHom.comp_apply (uT β hunit) ι,
      uT_comp_ι β hunit ι hD hι N]
    show (1 : S₁) ⊗ₜ[R₁] (algebraMap B₁ (BC β DA) a) * ((1 : S₁) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[B] (1 : DA))) = _
    rw [algebraMap_bc]
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  · intro d
    rw [RingHom.comp_apply, show (1 : Over β) = ov β 1 from rfl, vE_tmul, map_one, bwd₁_tmul, map_one, one_mul]
    rfl

def equiv₁ : S₁ ⊗[R₁] BC β DA ≃+* K₁ ⊗[B] DA :=
  RingEquiv.ofRingHom (fwd₁ β ι hBK hD hι) (bwd₁ β ι hBK hD hι hunit N) (by
    apply ringHom_ext
    · intro a
      rw [RingHom.comp_apply, bwd₁_tmul, one_tmul_one_bc, mul_one,
        ← RingHom.comp_apply, fwd₁_comp_uT]
      rfl
    · intro d
      rw [RingHom.comp_apply, bwd₁_tmul, map_one, one_mul, fwd₁_tmul, map_one,
        show (1 : Over β) = ov β 1 from rfl, vE_tmul, map_one]
      simp [Algebra.TensorProduct.tmul_mul_tmul]) (by
    apply ringHom_ext
    · intro s
      rw [RingHom.comp_apply, fwd₁_tmul, map_one, mul_one, bwd₁_tmul, one_tmul_one_bc, mul_one,
        uT_algebraMap]
      rfl
    · intro z
      rw [RingHom.comp_apply, fwd₁_tmul, map_one, ← Algebra.TensorProduct.one_def, one_mul,
        ← RingHom.comp_apply, bwd₁_comp_vE]
      rfl)

theorem equiv₁_tmul_one (s : S₁) :
    equiv₁ β ι hBK hD hι hunit N (s ⊗ₜ[R₁] (1 : BC β DA)) = algebraMap S₁ K₁ s ⊗ₜ[B] (1 : DA) := by
  show fwd₁ β ι hBK hD hι (s ⊗ₜ[R₁] (1 : BC β DA)) = _
  rw [fwd₁_tmul, map_one, mul_one]

end FirstIso2

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

section SecondIso

variable {K K₁ B DA : Type} [CommRing K] [CommRing K₁] [CommRing B] [CommRing DA] [Algebra K K₁]
  [Algebra B DA] [Algebra B K₁] (γ : B →+* K) (hBK : algebraMap B K₁ = (algebraMap K K₁).comp γ)

def fwd₂ : K₁ ⊗[K] BC γ DA →+* K₁ ⊗[B] DA :=
  tensorLift Algebra.TensorProduct.includeLeftRingHom (vE γ (algebraMap K K₁) hBK) (by
    apply RingHom.ext; intro k
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_bc, vE_tmul]
    rfl)

theorem fwd₂_tmul (a : K₁) (z : BC γ DA) :
    fwd₂ γ hBK (a ⊗ₜ[K] z) = (a ⊗ₜ[B] (1 : DA)) * vE γ (algebraMap K K₁) hBK z := by
  unfold fwd₂
  exact tensorLift_tmul _ _ _ a z

def bwd₂ : K₁ ⊗[B] DA →+* K₁ ⊗[K] BC γ DA :=
  tensorLift (R := B) Algebra.TensorProduct.includeLeftRingHom
    ((Algebra.TensorProduct.includeRight : BC γ DA →ₐ[K] K₁ ⊗[K] BC γ DA).toRingHom.comp
      (Algebra.TensorProduct.includeRight : DA →ₐ[B] BC γ DA).toRingHom) (by
    apply RingHom.ext; intro b
    rw [RingHom.comp_apply, hBK, RingHom.comp_apply]
    show algebraMap K K₁ (γ b) ⊗ₜ[K] (1 : BC γ DA) = (1 : K₁) ⊗ₜ[K] ((1 : Over γ) ⊗ₜ[B] algebraMap B DA b)
    rw [algebraMap_tmul_one, algebraMap_bc, tmul_one_bc])

theorem bwd₂_tmul (a : K₁) (d : DA) :
    bwd₂ γ hBK (a ⊗ₜ[B] d) = (a ⊗ₜ[K] (1 : BC γ DA)) * ((1 : K₁) ⊗ₜ[K] ((1 : Over γ) ⊗ₜ[B] d)) := by
  unfold bwd₂
  exact tensorLift_tmul _ _ _ a d

theorem bwd₂_comp_vE :
    (bwd₂ γ hBK).comp (vE γ (algebraMap K K₁) hBK) =
      (Algebra.TensorProduct.includeRight : BC γ DA →ₐ[K] K₁ ⊗[K] BC γ DA).toRingHom := by
  apply ringHom_ext (A := Over γ)
  · intro (a : K)
    change (bwd₂ γ hBK) ((vE γ (algebraMap K K₁) hBK) (ov γ a ⊗ₜ[B] (1 : DA))) = _
    rw [vE_tmul, bwd₂_tmul, one_tmul_one_bc, mul_one, algebraMap_tmul_one, algebraMap_bc]
    rfl
  · intro d
    rw [RingHom.comp_apply, show (1 : Over γ) = ov γ 1 from rfl, vE_tmul, map_one, bwd₂_tmul,
      ← Algebra.TensorProduct.one_def, one_mul]
    rfl

def equiv₂ : K₁ ⊗[K] BC γ DA ≃+* K₁ ⊗[B] DA :=
  RingEquiv.ofRingHom (fwd₂ γ hBK) (bwd₂ γ hBK) (by
    apply ringHom_ext
    · intro a
      rw [RingHom.comp_apply, bwd₂_tmul, one_tmul_one_bc, mul_one, fwd₂_tmul, map_one, mul_one]
      rfl
    · intro d
      rw [RingHom.comp_apply, bwd₂_tmul, ← Algebra.TensorProduct.one_def, one_mul, fwd₂_tmul,
        show (1 : Over γ) = ov γ 1 from rfl, vE_tmul, map_one]
      simp [Algebra.TensorProduct.tmul_mul_tmul]) (by
    apply ringHom_ext
    · intro a
      rw [RingHom.comp_apply, fwd₂_tmul, map_one, mul_one, bwd₂_tmul, one_tmul_one_bc, mul_one]
      rfl
    · intro z
      rw [RingHom.comp_apply, fwd₂_tmul, ← Algebra.TensorProduct.one_def, one_mul,
        ← RingHom.comp_apply, bwd₂_comp_vE]
      rfl)

theorem equiv₂_symm_tmul_one (a : K₁) :
    (equiv₂ γ hBK).symm (a ⊗ₜ[B] (1 : DA)) = a ⊗ₜ[K] (1 : BC γ DA) := by
  show bwd₂ γ hBK (a ⊗ₜ[B] (1 : DA)) = _
  rw [bwd₂_tmul, one_tmul_one_bc, mul_one]

end SecondIso

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

theorem isUnit_tmul_one {R₁ B₁ S₁ B DA : Type} [CommRing R₁] [CommRing B₁] [CommRing S₁] [IsDomain S₁]
    [IsDiscreteValuationRing S₁] [CommRing B] [CommRing DA] [Algebra R₁ B₁] [Algebra R₁ S₁]
    [Algebra B DA] (β : B →+* B₁) [Algebra R₁ (BC β DA)]
    (hD : algebraMap R₁ (BC β DA) = (algebraMap B₁ (BC β DA)).comp (algebraMap R₁ B₁))
    (x : R₁) (hx0 : algebraMap R₁ S₁ x ≠ 0) (hxu : ¬ IsUnit (algebraMap R₁ S₁ x))
    (hxB : IsUnit (algebraMap R₁ B₁ x)) :
    ∀ s ∈ nonZeroDivisors S₁, IsUnit (s ⊗ₜ[R₁] (1 : BC β DA)) := by
  intro s hs
  obtain ⟨n, hn⟩ := exists_dvd_pow (nonZeroDivisors.ne_zero hs) hx0 hxu
  have hu : IsUnit ((algebraMap R₁ S₁ x) ⊗ₜ[R₁] (1 : BC β DA)) := by
    rw [algebraMap_tmul_one, hD, RingHom.comp_apply]
    exact (hxB.map (algebraMap B₁ (BC β DA))).map
      (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S₁ ⊗[R₁] BC β DA)
  have h := map_dvd (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[R₁] BC β DA) hn
  rw [map_pow] at h
  exact isUnit_of_dvd_unit h (hu.pow n)

end GlobalTheory.KeyOriginTransport

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

theorem etale_closure_core
    (H : ∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
      [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
      [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
      [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
      Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
      ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
      ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
      GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
      Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M)))
    (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]
    (hAR : Function.Injective (algebraMap A R))
    (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁]
    (hAR₁ : Function.Injective (algebraMap A₁ R₁)) (φ : R →+* R₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁)
    (hβ : β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ)
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)) (hq : 0 < q)
    (htor : GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act)
    (S S₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁] [IsDomain S₁]
    [IsDiscreteValuationRing S₁] [Algebra R S] [Algebra R₁ S₁] [Algebra S S₁]
    (hRS : Function.Injective (algebraMap R S)) (hR₁S₁ : Function.Injective (algebraMap R₁ S₁))
    (hloc : ∀ r : R, algebraMap S S₁ (algebraMap R S r) = algebraMap R₁ S₁ (φ r))
    (hSS₁ : Function.Injective (algebraMap S S₁)) (hqS : IsUnit (q : S))
    (ϖ : S) (hϖ : Irreducible ϖ) (y : S₁) (hy : y ^ q = algebraMap S S₁ ϖ)
    (x : R₁) (hx0 : algebraMap R₁ S₁ x ≠ 0) (hxu : ¬ IsUnit (algebraMap R₁ S₁ x))
    (hxB : IsUnit (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) x)) :
    letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (BC β DA)).toAlgebra
    Algebra.Etale S₁ (integralClosure S₁ (S₁ ⊗[R₁] BC β DA)) := by
  haveI : FaithfulSMul S (FractionRing S₁) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ?_
    rw [IsScalarTower.algebraMap_eq S S₁ (FractionRing S₁)]
    exact (IsFractionRing.injective S₁ (FractionRing S₁)).comp hSS₁
  letI algKK₁ : Algebra (FractionRing S) (FractionRing S₁) := FractionRing.liftAlgebra S (FractionRing S₁)
  haveI : IsScalarTower S (FractionRing S) (FractionRing S₁) := FractionRing.isScalarTower_liftAlgebra _ _
  let γ : GlobalTheory.LocAcyc.GenFib A R →+* FractionRing S :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
      (g := (algebraMap S (FractionRing S)).comp (algebraMap R S)) (by
      rintro ⟨_, a, ha, rfl⟩
      refine isUnit_iff_ne_zero.2 ?_
      simp only [RingHom.comp_apply]
      intro h
      have h1 := (injective_iff_map_eq_zero _).1 (IsFractionRing.injective S (FractionRing S)) _ h
      have h2 := (injective_iff_map_eq_zero _).1 hRS _ h1
      have h3 := (injective_iff_map_eq_zero _).1 hAR _ h2
      exact nonZeroDivisors.ne_zero ha h3)
  let ι : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing S₁ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
      (g := (algebraMap S₁ (FractionRing S₁)).comp (algebraMap R₁ S₁)) (by
      rintro ⟨_, a, ha, rfl⟩
      refine isUnit_iff_ne_zero.2 ?_
      simp only [RingHom.comp_apply]
      intro h
      have h1 := (injective_iff_map_eq_zero _).1 (IsFractionRing.injective S₁ (FractionRing S₁)) _ h
      have h2 := (injective_iff_map_eq_zero _).1 hR₁S₁ _ h1
      have h3 := (injective_iff_map_eq_zero _).1 hAR₁ _ h2
      exact nonZeroDivisors.ne_zero ha h3)
  have hι : ι.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
      (algebraMap S₁ (FractionRing S₁)).comp (algebraMap R₁ S₁) := IsLocalization.lift_comp _
  letI algBK₁ : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) :=
    ((algebraMap (FractionRing S) (FractionRing S₁)).comp γ).toAlgebra
  have hBK₂ : algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) =
      (algebraMap (FractionRing S) (FractionRing S₁)).comp γ := rfl
  have hBK₁ : algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing S₁) = ι.comp β := by
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
    apply RingHom.ext; intro r
    rw [hBK₂, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ← RingHom.comp_apply β, hβ, RingHom.comp_apply]
    have e1 : γ (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r) =
        algebraMap S (FractionRing S) (algebraMap R S r) := IsLocalization.lift_eq _ _
    have e2 : ι (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) (φ r)) =
        algebraMap S₁ (FractionRing S₁) (algebraMap R₁ S₁ (φ r)) := IsLocalization.lift_eq _ _
    rw [e1, e2, ← IsScalarTower.algebraMap_apply S (FractionRing S) (FractionRing S₁),
      IsScalarTower.algebraMap_apply S S₁ (FractionRing S₁), hloc]
  letI algD : Algebra R₁ (BC β DA) := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (BC β DA)).toAlgebra
  have hD : algebraMap R₁ (BC β DA) =
      (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) (BC β DA)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) := rfl
  have hunit := isUnit_tmul_one (S₁ := S₁) β hD x hx0 hxu hxB
  let e₁ := equiv₁ β ι hBK₁ hD hι hunit (Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  let e₂ := equiv₂ (K₁ := FractionRing S₁) (DA := DA) γ hBK₂
  let e : (S₁ ⊗[R₁] BC β DA) ≃ₐ[S₁] (FractionRing S₁ ⊗[FractionRing S] BC γ DA) :=
    AlgEquiv.ofRingEquiv (f := e₁.trans e₂.symm) (fun s => by
      rw [RingEquiv.trans_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, equiv₁_tmul_one, equiv₂_symm_tmul_one, Algebra.TensorProduct.algebraMap_apply])
  have hE := H S S₁ (FractionRing S) (FractionRing S₁) hSS₁ q hq hqS ϖ hϖ y hy
    (BC γ DA) (bcAct γ DA q act) (isZTorsor_bc γ DA q hq act htor)
  exact Algebra.Etale.of_equiv (AlgEquiv.mapIntegralClosure e.symm)

end GlobalTheory.KeyOriginTransport
end
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

theorem etale_closure_of_field : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  intro H A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hAR₁ f hf φ hφ β hβ DA _ _ q act hq hqA htor P₁ _ hS₁ hS π hπ y hy
  haveI := hS₁
  haveI := hS
  letI algSS₁ : Algebra (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) :=
    (Localization.localRingHom (P₁.comap φ) P₁ φ rfl).toAlgebra
  have hloc : ∀ r : R, algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
      (algebraMap R (Localization.AtPrime (P₁.comap φ)) r) = algebraMap R₁ (Localization.AtPrime P₁) (φ r) :=
    Localization.localRingHom_to_map _ _ _ rfl
  have hR₁S₁ : Function.Injective (algebraMap R₁ (Localization.AtPrime P₁)) :=
    IsLocalization.injective _ P₁.primeCompl_le_nonZeroDivisors
  have hRS : Function.Injective (algebraMap R (Localization.AtPrime (P₁.comap φ))) :=
    IsLocalization.injective _ (P₁.comap φ).primeCompl_le_nonZeroDivisors
  have hπS : algebraMap A (Localization.AtPrime (P₁.comap φ)) π =
      algebraMap R (Localization.AtPrime (P₁.comap φ)) (algebraMap A R π) :=
    IsScalarTower.algebraMap_apply A R _ π
  have hφw : φ (algebraMap A R π) = algebraMap A₁ R₁ (f π) := by
    rw [← RingHom.comp_apply, hφ]; rfl
  have hπ0 : f π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    have h0 : π = 0 := (injective_iff_map_eq_zero f).1 hf π h
    rw [h0, map_zero]
  have hx0 : algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π)) ≠ 0 := by
    rw [hφw]
    intro h
    exact hπ0 ((injective_iff_map_eq_zero _).1 hAR₁ _ ((injective_iff_map_eq_zero _).1 hR₁S₁ _ h))
  have hxu : ¬ IsUnit (algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π))) := by
    intro hu
    rw [← hloc] at hu
    haveI := Localization.isLocalHom_localRingHom (P₁.comap φ) P₁ φ rfl
    apply hπ.not_isUnit
    rw [hπS]
    exact isUnit_of_map_unit (Localization.localRingHom (P₁.comap φ) P₁ φ rfl) _ hu
  have hSS₁ : Function.Injective
      (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0'
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0' hπ
    have h2 := hn.map (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁))
    rw [hx, map_pow, hπS, hloc] at h2
    exact pow_ne_zero n hx0 (h2.eq_zero_iff.1 rfl)
  have hqS : IsUnit ((q : Localization.AtPrime (P₁.comap φ))) := by
    have := hqA.map (algebraMap A (Localization.AtPrime (P₁.comap φ)))
    rwa [map_natCast] at this
  have hy' : (algebraMap R₁ (Localization.AtPrime P₁) y) ^ q =
      algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
        (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) := by
    rw [← map_pow, hy, hπS, hloc]
  have hxB : IsUnit (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) (φ (algebraMap A R π))) := by
    rw [hφw]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (f π), f π, mem_nonZeroDivisors_of_ne_zero hπ0, rfl⟩ :
        Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  exact etale_closure_core H A R hAR A₁ R₁ hAR₁ φ β hβ DA q act hq htor
    (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) hRS hR₁S₁ hloc hSS₁ hqS
    (algebraMap A _ π) hπ (algebraMap R₁ _ y) hy' (φ (algebraMap A R π)) hx0 hxu hxB

end GlobalTheory.KeyOriginTransport
end
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  first | (exact @GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (exact GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (intros; apply GlobalTheory.KeyOriginTransport.etale_closure_of_field  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AbhHeightOne

theorem closureEtaleAt_of_etale_integralClosure_localization : ∀ (A₁ R₁ D₁ : Type) [CommRing A₁] [CommRing R₁] [Algebra A₁ R₁] [CommRing D₁]
    [Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) D₁] (P₁ : Ideal R₁) [P₁.IsPrime],
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁))) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ D₁ P₁ := by
  intro A₁ R₁ D₁ _ _ _ _ _ P₁ _ h
  letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ R₁ D₁
  unfold GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt
  let e : GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[R₁] integralClosure R₁ D₁ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R₁)
    (S := Localization.AtPrime P₁) (B := D₁) P₁.primeCompl
  let Φ : Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[Localization.AtPrime P₁]
      integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (AlgEquiv.ofBijective _ hb)
  exact Algebra.Etale.of_equiv Φ.symm

theorem etale_integralClosure_of_torsor_field : ∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M)) := by
  intro S S₁ K K₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy M _ _ act htor
  obtain ⟨ι, _, L, _, _, hfd, hgal, hdeg, ⟨e⟩⟩ := GlobalTheory.T.zmodTorsor_field_eq_prod_galois K M q act hq htor
  have hi : ∀ i, Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L i)) := fun i => by
    letI : Algebra S (L i) := ((algebraMap K (L i)).comp (algebraMap S K)).toAlgebra
    haveI : IsScalarTower S K (L i) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI := hfd i
    haveI := hgal i
    obtain ⟨hram, hsep⟩ := GlobalTheory.T.ramificationIdx_dvd_of_galois_degree_dvd_unit_dvr S K (L i) q hq hqu (hdeg i)
    exact GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer S S₁ K K₁ (L i) hinj q hq hqu π hπ y hy hram hsep
  classical
  haveI := GlobalTheory.T.etale_integralClosure_pi_of_etale S₁ ι (fun i => K₁ ⊗[K] L i) hi
  let Ψ : K₁ ⊗[K] M ≃ₐ[K₁] ∀ i, K₁ ⊗[K] L i :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (Algebra.TensorProduct.piRight K K₁ K₁ L)
  exact Algebra.Etale.of_equiv (Ψ.restrictScalars S₁).symm.mapIntegralClosure

theorem closureEtaleAt_of_root_of_uniformiser : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA) P₁ := by
  intro A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hA₁R₁ f hf φ hφ β hβ DA _ _ q act hq hqu htor P₁ _ hd₁ hd π hπ y hy
  exact closureEtaleAt_of_etale_integralClosure_localization A₁ R₁ _ P₁ (GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields etale_integralClosure_of_torsor_field A R hAR A₁ R₁ hA₁R₁ f hf φ hφ β hβ DA q act hq hqu htor P₁ hd₁ hd π hπ y hy)

end GlobalTheory.AbhHeightOne
end
end
