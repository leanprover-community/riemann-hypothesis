import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankFixedSubmoduleComplexification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValue
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universalTripleFibre_at_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  first | exact @GlobalTheory.KeyFourth.exists_tied | exact GlobalTheory.KeyFourth.exists_tied | (intros; apply GlobalTheory.KeyFourth.exists_tied <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_triple_fibres_base_change_key_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  first | exact @GlobalTheory.KeyFourth.tied_keyPB | exact GlobalTheory.KeyFourth.tied_keyPB | (intros; apply GlobalTheory.KeyFourth.tied_keyPB <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  first | exact @GlobalTheory.KeyFourth.rule_frBor | exact GlobalTheory.KeyFourth.rule_frBor | (intros; apply GlobalTheory.KeyFourth.rule_frBor <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_rule_value_at_theta_point : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  first | exact @GlobalTheory.KeyFourth.value_at_thetaPt | exact GlobalTheory.KeyFourth.value_at_thetaPt | (intros; apply GlobalTheory.KeyFourth.value_at_thetaPt <;> assumption)
end

section
open Polynomial

namespace GlobalTheory.ContRoot

open GlobalTheory.AffinePoints

theorem nonempty_algHom (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem exists_monic_prime_dvd (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    {n : ℕ} (hn : 0 < n) (u : B) :
    ∃ P : B[X], P.Monic ∧ Prime P ∧ 0 < P.natDegree ∧ P ∣ X ^ n - C u := by
  let L := AlgebraicClosure (FractionRing B)
  have hinj : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B (FractionRing B) L]
    exact (algebraMap (FractionRing B) L).injective.comp (IsFractionRing.injective B _)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).2 hinj
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B L u) hn
  have h0 : aeval β (X ^ n - C u : B[X]) = 0 := by simp [hβ]
  have hint : IsIntegral B β := ⟨_, monic_X_pow_sub_C u hn.ne', h0⟩
  exact ⟨minpoly B β, minpoly.monic hint, minpoly.prime_of_isIntegrallyClosed hint,
    minpoly.natDegree_pos hint, minpoly.isIntegrallyClosed_dvd hint h0⟩

theorem exists_pow_eq_of_continuous_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  intro B _ _ _ _ n u ρ hn hc hρ
  have hρc : Continuous ρ := GlobalTheory.RootConst.continuous_of_holomorphic_families B ρ hc
  have := GlobalTheory.isIntegrallyClosed_of_smooth ℂ B
  obtain ⟨P, hm, hp, hd, hdvd⟩ := exists_monic_prime_dvd B hn (u : B)
  have hdom : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hp
  have hft : Algebra.FiniteType ℂ (AdjoinRoot P) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have hconn := GlobalTheory.RootConst.preconnectedSpace_algHom (AdjoinRoot P)
  let φ : B →ₐ[ℂ] AdjoinRoot P := IsScalarTower.toAlgHom ℂ B (AdjoinRoot P)
  have hroot : AdjoinRoot.root P ^ n = φ u := by
    have h := (AdjoinRoot.mk_eq_zero (f := P)).2 hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  have hu : ∀ ψ : B →ₐ[ℂ] ℂ, ψ u ≠ 0 := fun ψ => (u.isUnit.map ψ).ne_zero
  have hρ0 : ∀ ψ, ρ ψ ≠ 0 := fun ψ h => hu ψ (by rw [← hρ, h, zero_pow hn.ne'])
  have hcont : Continuous fun χ : AdjoinRoot P →ₐ[ℂ] ℂ =>
      χ (AdjoinRoot.root P) / ρ (comap φ χ) :=
    (continuous_eval _).div (hρc.comp (continuous_comap φ)) fun _ => hρ0 _
  have hconst := GlobalTheory.RootConst.eq_of_pow_eq_one hcont hn fun χ => by
    rw [div_pow, ← map_pow, hroot, hρ, comap_apply]
    exact div_self (hu (comap φ χ))
  obtain ⟨ψ⟩ := nonempty_algHom B
  have key : ∀ z, (P.map (ψ : B →+* ℂ)).IsRoot z → ∃ χ : AdjoinRoot P →ₐ[ℂ] ℂ,
      comap φ χ = ψ ∧ χ (AdjoinRoot.root P) = z := by
    intro z hz
    have hz' : P.eval₂ (ψ : B →+* ℂ) z = 0 := by rw [← eval_map]; exact hz
    refine ⟨AdjoinRoot.liftAlgHom P ψ z hz', ?_, by simp⟩
    ext b
    simp [φ]
  have huniq : ∀ z w, (P.map (ψ : B →+* ℂ)).IsRoot z → (P.map (ψ : B →+* ℂ)).IsRoot w →
      z = w := by
    intro z w hz hw
    obtain ⟨χ, h1, h2⟩ := key z hz
    obtain ⟨χ', h1', h2'⟩ := key w hw
    have h := hconst χ χ'
    simp only [h1, h1', h2, h2'] at h
    exact (div_left_inj' (hρ0 ψ)).1 h
  have hsep : (P.map (ψ : B →+* ℂ)).Separable := by
    refine (separable_X_pow_sub_C (n := n) (ψ u) (Nat.cast_ne_zero.2 hn.ne') (hu ψ)).of_dvd ?_
    simpa using Polynomial.map_dvd (ψ : B →+* ℂ) hdvd
  have hne : P.map (ψ : B →+* ℂ) ≠ 0 := (hm.map _).ne_zero
  have hdeg : P.natDegree ≤ 1 := by
    rw [← hm.natDegree_map (ψ : B →+* ℂ),
      (IsAlgClosed.splits (P.map (ψ : B →+* ℂ))).natDegree_eq_card_roots,
      ← Multiset.toFinset_card_of_nodup (nodup_roots hsep)]
    refine Finset.card_le_one.2 fun a ha b hb => huniq a b ?_ ?_
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 ha)
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 hb)
  have h1 : P = X + C (P.coeff 0) := hm.eq_X_add_C (le_antisymm hdeg hd)
  refine ⟨-P.coeff 0, ?_⟩
  have h2 : P.eval (-P.coeff 0) = 0 := by
    rw [congrArg (eval (-P.coeff 0)) h1]; simp
  have h3 := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h2
  simpa [sub_eq_zero] using h3

end GlobalTheory.ContRoot
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  atlas_forward_decl GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root
end

section
section
open scoped TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_of_pow_eq_pow {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    {n : ℕ} (hn : 0 < n) {x y : R} (h : x ^ n = y ^ n) : ∃ z : ℂ, x = z • y := by
  have : NeZero n := ⟨hn.ne'⟩
  have h0 := Complex.isPrimitiveRoot_exp n hn.ne'
  have h1 := h0.map_of_injective (algebraMap ℂ R).injective
  have h2 := h1.pow_sub_pow_eq_prod_sub_mul x y hn
  rw [h, sub_self] at h2
  obtain ⟨ζ, hζ, hz⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [Polynomial.mem_nthRootsFinset hn] at hζ
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / n) ^ i, ?_⟩
  rw [Algebra.smul_def, map_pow, hi]
  exact sub_eq_zero.1 hz

theorem exists_eq_smul_pow_of_pow_eq_tmul :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A]
      [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 →
      w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  intro K _ _ A _ _ _ n w C u hn hC hu hw
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : ℂ) ≠ 0)
  let T : ℂ ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap ∘ₗ LinearMap.rTensor A f
  have hT : ∀ (c : ℂ) (a : A), T (c ⊗ₜ a) = f c • a := fun c a => by simp [T]
  have hne : ∀ (c : ℂ) (a : A), c ≠ 0 → a ≠ 0 → c ⊗ₜ[K] a ≠ 0 := by
    intro c a hc ha h
    have h1 : (1 : ℂ) ⊗ₜ[K] a = 0 := by
      have := congrArg (fun t : ℂ ⊗[K] A => c⁻¹ • t) h
      simpa [TensorProduct.smul_tmul', hc] using this
    have h2 := hT 1 a
    rw [h1, map_zero, hf, one_smul] at h2
    exact ha h2.symm
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hw
    exact hne C u hC hu hw.symm
  have hst : ∀ σ : ℂ ≃ₐ[K] ℂ, ∀ x ∈ Submodule.span ℂ {w},
      σ.toLinearMap.rTensor A x ∈ Submodule.span ℂ {w} := by
    intro σ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    let S : ℂ ⊗[K] A →ₐ[K] ℂ ⊗[K] A := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
    have hS : ∀ t, σ.toLinearMap.rTensor A t = S t := by
      intro t
      induction t with
      | zero => simp
      | tmul b v => simp [S]
      | add x y hx hy => simp only [map_add, hx, hy]
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (σ C / C) hn
    have h1 : (S w) ^ n = (μ • w) ^ n := by
      rw [← map_pow, smul_pow, hw, hμ, TensorProduct.smul_tmul', smul_eq_mul,
        div_mul_cancel₀ _ hC]
      simp [S]
    obtain ⟨z, hz⟩ := exists_eq_smul_of_pow_eq_pow hn h1
    have h2 : c • w = (c ⊗ₜ[K] (1 : A)) * w := by
      rw [Algebra.smul_def]; rfl
    have h3 : S (c ⊗ₜ[K] (1 : A)) * S w = σ c • S w := by
      rw [Algebra.smul_def]
      simp [S]
    rw [hS, h2, map_mul, h3, hz, smul_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  obtain ⟨N, hN, -⟩ := (GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange _).1 hst
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    rw [Submodule.baseChange_bot, eq_comm, Submodule.span_singleton_eq_bot] at hN
    exact hw0 hN
  obtain ⟨b, hbN, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hb : (1 : ℂ) ⊗ₜ[K] b ∈ Submodule.span ℂ {w} :=
    hN ▸ Submodule.tmul_mem_baseChange_of_mem 1 hbN
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hb
  have hpow : (1 : ℂ) ⊗ₜ[K] (b ^ n) = (l ^ n * C) ⊗ₜ[K] u := by
    have := congrArg (· ^ n) hl
    simp only [smul_pow, hw, Algebra.TensorProduct.tmul_pow, one_pow, TensorProduct.smul_tmul',
      smul_eq_mul] at this
    exact this.symm
  have hbn : b ^ n ≠ 0 := by
    intro h
    have h1 : ((1 : ℂ) ⊗ₜ[K] b) ^ n = 0 := by
      rw [Algebra.TensorProduct.tmul_pow, h, TensorProduct.tmul_zero]
    exact hne 1 b one_ne_zero hb0 (pow_eq_zero_iff hn.ne' |>.1 h1)
  have h4 := congrArg T hpow
  rw [hT, hT, hf, one_smul] at h4
  have h5 : f (l ^ n * C) ≠ 0 := by
    intro h
    rw [h, zero_smul] at h4
    exact hbn h4
  exact ⟨(f (l ^ n * C))⁻¹, b, inv_ne_zero h5, by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩

end GlobalTheory.KeyFourth
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification : ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A] [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 → w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  atlas_forward_decl GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_exponent_section_of_chart_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  first | exact @GlobalTheory.SecGlueInt.exists_secZ_of_regular | exact GlobalTheory.SecGlueInt.exists_secZ_of_regular | (intros; apply GlobalTheory.SecGlueInt.exists_secZ_of_regular <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_keySection_complexValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (T : ∀ k, ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → (∀ k, IsNormUn (T k) (un k)) → FramesOK e F M un → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (ρ : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → (∀ b ∈ B, RootVal (unfOf e F M un) (y b) (ρ b)) → ContinuousOn ρ B := by
  first | exact @GlobalTheory.KeyFourth.continuousOn_rootVal | exact GlobalTheory.KeyFourth.continuousOn_rootVal | (intros; apply GlobalTheory.KeyFourth.continuousOn_rootVal <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_pow {K : Type} [Field K] [Algebra K ℂ] {A : Type} [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] [IsDomain (ℂ ⊗[K] A)] {n : ℕ} (hn : 0 < n) (u : Aˣ) {C : ℂ} (hC : C ≠ 0)
    (ρ : (A →ₐ[K] ℂ) → ℂ)
    (hρ : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (A →ₐ[K] ℂ)), IsOpen V →
      (∀ a : A, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V)
    (hu : ∀ ψ : A →ₐ[K] ℂ, ρ ψ ^ n = C * ψ (u : A)) : ∃ (a : K) (b : A), a ≠ 0 ∧ (u : A) = a • b ^ n := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (ℂ ⊗[K] A) inferInstance
  let res : (ℂ ⊗[K] A →ₐ[ℂ] ℂ) → (A →ₐ[K] ℂ) := fun χ =>
    (χ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let u' : (ℂ ⊗[K] A)ˣ := Units.map (algebraMap ℂ (ℂ ⊗[K] A) : ℂ →* _) (Units.mk0 C hC) *
    Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] ℂ ⊗[K] A) : A →* _) u
  have hu' : (u' : ℂ ⊗[K] A) = C ⊗ₜ[K] (u : A) := by
    simp [u', Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root (ℂ ⊗[K] A) n u' (fun χ => ρ (res χ)) hn
    (fun m V s hV hs => hρ m V (fun p => res (s p)) hV fun a => hs _) (fun χ => by
      rw [hu, hu']
      have : C ⊗ₜ[K] (u : A) = C • ((1 : ℂ) ⊗ₜ[K] (u : A)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl)
  exact GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification K A n w C u hn hC u.ne_zero (hw.trans hu')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem keySec_of_generic (h : GenFrEx Xo c) (b : ∀ Z : Comp Xo c, Om Z) (hb0 : ∀ Z, b Z ≠ 0)
    (hb : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R) : Nonempty (KeySec Xo c) := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (keyEx Dw) b fun C => (hb C).1
  obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-keyEx Dw) (fun Z => (b Z)⁻¹) fun C => by
    have := (hb C).2
    rw [mul_inv, ← Units.val_inv_eq_inv_val] at this
    simpa only [kch, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] using this
  have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
    rw [← GlobalTheory.AllWt.secZ_nat]
    congr 1
    funext i
    cases i <;> rfl
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, h0] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [h0] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
    have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
    have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
      (f * f') 1
    refine e₃.trans ?_
    change evC h Z (f * f') - evC h Z 1 = 0
    rw [e₁, e₂, hfb, hfb', mul_inv_cancel₀ (hb0 Z), sub_self]
  exact ⟨⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf⟩⟩

theorem exists_chart_units {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.FamUnit κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (hpq : 1 ≤ Dw.p + Dw.q)
    (h : GenFrEx Xo c) : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
        ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨Φ, u, hΦ, hu, ?_⟩
  rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem rule_eq_of_rootVal {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.ThetaOne κ) {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1)} {r : ℕ} {M : ModelsOf F r} (T : ∀ k, ThetaData e F M k)
    {un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)} (hun : ∀ k, IsNormUn (T k) (un k)) (hpq : 1 ≤ Dw.p + Dw.q)
    {N : ℂ} (hN : N ≠ 0) (hNk : ∀ k, (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) = N)
    {y : FrPt Xo c (CAt σ)} {v : ℂ} (hv : RootVal (unfOf e F M un) y v) (Φ : FibKey Xo ℂ y.x)
    (hΦ : Tied (S := ℂ) e y.s y.u Φ) :
    v ^ 4 = (N / (2 * Real.pi * Complex.I) ^ g) ^ 4 * (κ ℂ Φ.key : ℂ) := by
  obtain ⟨k, x, t, ht, rfl⟩ : ∃ (k : Fin F.n) (x : (M.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) := hv
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (un k x).x, Tied (S := ℂ) e (un k x).s (un k x).u Ψ :=
    @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (un k x) hpq
  have e₁ : κ ℂ Φ.key = kch (S := ℂ) t ^ 4 * κ ℂ Ψ.key :=
    @GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra t (un k x) y Ψ Φ ht hΨ hΦ
  obtain ⟨a, ha, hy⟩ := hun k x
  have hb : (T k).co.symm x.1 ∈ (T k).co ⁻¹' (M.X k).dom := by
    show (T k).co ((T k).co.symm x.1) ∈ (M.X k).dom
    rw [(T k).co.apply_symm_apply]; exact x.2
  have d1 := ((T k).norm _ hb).1.ne_zero
  rw [hNk] at ha
  have a0 : a ≠ 0 := fun h0 => mul_ne_zero hN d1 (by rw [← ha, h0]; simp)
  have e₂ := GlobalTheory.T.theta_key_rule_value_at_theta_point κ h₁ h₃ E H Dw l Xo c σ g e F r M k (T k) _ hb a (un k x) Ψ a0 hy hΨ
  have e₃ : N ^ 4 * (κ ℂ Ψ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g) ^ 4 := by
    refine mul_right_cancel₀ (pow_ne_zero 4 d1) ?_
    rw [show a ^ 8 = (a ^ 2) ^ 4 by ring, ha] at e₂
    linear_combination e₂
  have hπ : ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Complex.two_pi_I_ne_zero)
  have e₄ : (κ ℂ Φ.key : ℂ) = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) ^ 4 * (κ ℂ Ψ.key : ℂ) := by
    rw [e₁]
    rfl
  rw [e₄, div_pow, mul_left_comm, div_mul_eq_mul_div, e₃, div_self hπ, mul_one]

set_option maxHeartbeats 1000000 in

theorem nonempty_keySec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → (∀ k la γ, (U.X k).χ la γ = 1) → FnAlgClosed Xo c → 2 ≤ N → 2 < Module.finrank ℚ E / 2 → Nonempty (KeySec Xo c) := by
  intro E _ _ _ H Dw l Xo c σ N U hσ hU _ _ hF hN _
  obtain ⟨hr, -, -, -, -, g, e, F, -⟩ := hU
  have hpq : 1 ≤ Dw.p + Dw.q := by omega
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F _ M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F _ M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨κ, k₁, k₂, -, k₃, -, k₄, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_chart_units k₁ k₂ k₄ e hpq h
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => GlobalTheory.T.continuousOn_keySection_complexValue E H Dw l Xo c σ g e F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e (z ψ).s (z ψ).u Ψ :=
          @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ hΨ).trans
          (congrArg _ (hu ℂ _ _
            (@GlobalTheory.T.universal_triple_fibres_base_change_key_data E _ _ _ H Dw l Xo c g e _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ (hz ψ) hΦ hΨ))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  refine keySec_of_generic h b hb0 fun C => ?_
  obtain ⟨-, u, -, -, huv⟩ := hv C
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
    have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
    exact hw ▸ w.2
  have hc : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
    rw [Algebra.smul_def]
    rfl
  have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
    rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ (ha _), one_smul, mul_pow]
  refine ⟨hint _ _ (e₁.trans (hc _ _).symm),
    hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
  rw [inv_pow, e₁, hc]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
  rfl

end GlobalTheory.KeyFourth
end
end
