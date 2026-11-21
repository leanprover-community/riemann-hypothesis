import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructureStatement
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponentsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalLevelUnitriangularIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents

section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∀ x : E, psi (inclE (F := F) (Ad F) x) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1) → ∀ (p : ℕ), p.Prime → SplitsIn E p → ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → ∀ e ∈ intV E v, e * e = e → e ≠ 0 → ∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((p : F)⁻¹) * (e * a))) ≠ 1 := by
  first | exact @GlobalTheory.St.G.psi_local_ne_one | exact GlobalTheory.St.G.psi_local_ne_one | (intros; apply GlobalTheory.St.G.psi_local_ne_one <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem intV_iff_sp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp), (∀ i, (gp i).Prime) → (∀ i, SplitsIn E (gp i)) → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : E ⊗[F] v.adicCompletion F), x ∈ intV E v ↔ (G.sp i v hv x).1 ∈ v.adicCompletionIntegers F ∧ (G.sp i v hv x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm gp G _ _ i v hv x
  exact split_integral_local F E v (G.sp i v hv) (G.sp_alg i v hv) x

end GlobalTheory.St.G
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_integers_iff_split_at_type_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp), (∀ i, (gp i).Prime) → (∀ i, SplitsIn E (gp i)) → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : E ⊗[F] v.adicCompletion F), x ∈ intV E v ↔ (G.sp i v hv x).1 ∈ v.adicCompletionIntegers F ∧ (G.sp i v hv x).2 ∈ v.adicCompletionIntegers F := by
  atlas_forward_decl GlobalTheory.St.G.intV_iff_sp
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FrLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) :
    prV (E := E) v (sigR σ (Ad F) a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) :=
  RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) a

theorem prV_OAd (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) :
    prV (E := E) v a ∈ intV E v :=
  ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 a).1 ha v

theorem prVec_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → E ⊗[F] Ad F) :
    prVec v (x + y) = prVec v x + prVec v y := by
  funext i; simp [prVec, map_add]

theorem prVec_zero (v : HeightOneSpectrum (𝓞 F)) : prVec v (0 : Fin n → E ⊗[F] Ad F) = 0 := by
  funext i; simp [prVec]

theorem prVec_smul (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (a • x) = prV (E := E) v a • prVec v x := by
  funext i; simp [prVec, map_mul]

theorem prVec_span (v : HeightOneSpectrum (𝓞 F)) (S : Set (Fin n → E ⊗[F] Ad F))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ Submodule.span (OAd F E) S) :
    prVec v x ∈ Submodule.span (intV E v) (prVec v '' S) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [prVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [prVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : prVec v (a • x) = (⟨prV (E := E) v a, prV_OAd v a.2⟩ : intV E v) • prVec v x :=
      prVec_smul v (a : E ⊗[F] Ad F) x
    rw [h]; exact Submodule.smul_mem _ _ hx

theorem prVec_hat (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ hat F L) : prVec v x ∈ loc v L := by
  have h := prVec_span v _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  exact ⟨l, hl, rfl⟩

theorem hR_prVec (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Ad F) :
    hR σ J (v.adicCompletion F) (prVec v x) (prVec v y) = prV (E := E) v (hR σ J (Ad F) x y) := by
  simp only [hR, hform, map_sum, map_mul, prV_sigR, prVec, Matrix.map_apply, Formalism.UG.P.afsplit_prV_inclE]

end GlobalTheory.St.G.FrLoc

open GlobalTheory.St.G.FrLoc in
theorem GlobalTheory.St.G.frame_component_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  intro F E _ _ _ _ _ σ n J L g k Fr v
  refine ⟨?_, ?_, prV_OAd v Fr.eps_int, ?_, fun i => prVec_hat v L (Fr.b_mem i),
    fun i => prVec_hat v L (Fr.bd_mem i), ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, Fr.eps_idem]
  · rw [← prV_sigR, ← map_mul, Fr.eps_orth, map_zero]
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨z, hz, hzeq⟩ := Fr.eps_full (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) hzeq
      rw [prVec_smul, prVec_smul, map_sub, map_sub, map_one, prV_sigR, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z₁, hz₁, e₁⟩ := hx
      obtain ⟨z₂, hz₂, e₂⟩ := hy
      exact ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [smul_add, smul_add, e₁, e₂]⟩
    | smul c x _ hx =>
      obtain ⟨z, hz, e⟩ := hx
      refine ⟨c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, smul_smul, mul_comm, ← smul_smul, e, smul_smul,
        smul_smul, mul_comm]
  · intro i
    have h := congrArg (prVec v) (Fr.b_eps i)
    rw [prVec_smul] at h
    exact h
  · intro i
    have h := congrArg (prVec v) (Fr.bd_eps i)
    rw [prVec_smul, prV_sigR] at h
    exact h
  · intro i j
    obtain ⟨t, ht, e⟩ := Fr.dual i j
    refine ⟨prV (E := E) v t, prV_OAd v ht, ?_⟩
    have h := congrArg (prV (E := E) v) e
    rw [map_sub, map_mul, map_natCast, ← hR_prVec, apply_ite (prV (E := E) v), map_zero] at h
    exact h
  · have hsub : prVec v '' (Set.range Fr.b ∪ Set.range Fr.bd) ⊆
        Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j)) := by
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inl ⟨j, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inr ⟨j, rfl⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨s, hs, z, hz, e⟩ := Fr.span (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v s, Submodule.span_mono hsub (prVec_span v _ hs), prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) e
      rw [prVec_add, prVec_smul, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s₁, hs₁, z₁, hz₁, e₁⟩ := hx
      obtain ⟨s₂, hs₂, z₂, hz₂, e₂⟩ := hy
      refine ⟨s₁ + s₂, add_mem hs₁ hs₂, z₁ + z₂, add_mem hz₁ hz₂, ?_⟩
      rw [e₁, e₂, smul_add]; abel
    | smul c x _ hx =>
      obtain ⟨s, hs, z, hz, e⟩ := hx
      refine ⟨c • s, Submodule.smul_mem _ c hs, c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [e, smul_add, Subring.smul_def, Subring.smul_def, Subring.smul_def, smul_smul, smul_smul,
        mul_comm]
end
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeFrame_component_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  atlas_forward_decl GlobalTheory.St.G.frame_component_local
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem not_forall_loc_eq_natCast_smul (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hdiag : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a))
    (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L) (hn : 0 < n) :
    ¬ ∀ y ∈ loc v L, ∃ z ∈ loc v L, y = (g : E ⊗[F] v.adicCompletion F) • z := by
  classical
  intro h
  have hs := split_integral_local F E v sp hdiag
  have hint : ∀ r ∈ intV E v, (sp r).1 ∈ v.adicCompletionIntegers F := fun r hr => ((hs r).1 hr).1
  have hOE : ∀ c : 𝓞 E, inclE (F := F) (v.adicCompletion F) (c : E) ∈ intV E v := by
    intro c
    have hc : ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ PI.SplitIntLoc.tensInt (v.adicCompletion F)
        (PI.SplitIntLoc.intOE E) (v.adicCompletionIntegers F).toSubring :=
      Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
    exact hc
  have hv : Valued.v ((g : v.adicCompletion F)) < 1 := by
    have h1 : v.intValuation (g : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hg
    have h2 : ((g : v.adicCompletion F)) = algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F) :=
      (map_natCast _ g).symm
    rw [h2]
    refine lt_of_eq_of_lt (v.valuedAdicCompletion_eq_valuation (g : 𝓞 F)) ?_
    rw [v.valuation_of_algebraMap]
    exact h1
  obtain ⟨hfin, hspan⟩ := hL
  obtain ⟨G, hG⟩ := Module.Finite.iff_fg.1 hfin
  have hgen : ∀ x ∈ L, (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc v L :=
    fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  set M : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F) := Submodule.span _
    (Set.range fun p : G × Fin n => (sp (inclE (F := F) (v.adicCompletion F) ((p.1 : Fin n → E) p.2))).1) with hMdef
  have hMx : ∀ x ∈ L, ∀ i, (sp (inclE (F := F) (v.adicCompletion F) (x i))).1 ∈ M := by
    intro x hx i
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem s hsG => exact Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using M.add_mem ha hb
    | smul c a _ ha =>
      have hc := hint _ (hOE c)
      have e : (sp (inclE (F := F) (v.adicCompletion F) ((c • a) i))).1 =
          (⟨_, hc⟩ : v.adicCompletionIntegers F) • (sp (inclE (F := F) (v.adicCompletion F) (a i))).1 := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ ha
  have hM : ∀ y ∈ loc v L, ∀ i, (sp (y i)).1 ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      exact hMx x hxL
    | zero => intro i; simp
    | add a b _ _ ha hb => intro i; simpa using M.add_mem (ha i) (hb i)
    | smul r a _ ha =>
      intro i
      have hr := hint _ r.2
      have e : (sp ((r • a) i)).1 = (⟨_, hr⟩ : v.adicCompletionIntegers F) • (sp (a i)).1 := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ (ha i)
  have hle : M ≤ Ideal.span {((g : v.adicCompletionIntegers F))} • M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨⟨s, hsG⟩, i⟩, rfl⟩
    have hsL : s ∈ L := hG ▸ Submodule.subset_span hsG
    obtain ⟨z, hz, hyz⟩ := h _ (hgen s hsL)
    have e : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 =
        (g : v.adicCompletionIntegers F) • (sp (z i)).1 := by
      have hi : inclE (F := F) (v.adicCompletion F) (s i) = ((g : E ⊗[F] v.adicCompletion F) • z) i :=
        congrFun hyz i
      rw [hi, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Prod.fst_mul, Algebra.smul_def]
      simp
    change (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈
      ((Ideal.span {((g : v.adicCompletionIntegers F))} • M : Submodule _ _) : Set (v.adicCompletion F))
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hM z hz i)
  have hjac : Ideal.span {((g : v.adicCompletionIntegers F))} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨b, hb⟩ := hunit.exists_left_inv
    have hb' : (b : v.adicCompletion F) * (g : v.adicCompletion F) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hbv : Valued.v (b : v.adicCompletion F) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).1 b.2
    have hlt : Valued.v ((b : v.adicCompletion F) * (g : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' hbv).trans_lt hv
    rw [hb', map_one] at hlt
    exact lt_irrefl _ hlt
  have hne : ∃ s ∈ G, ∃ i, s i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hL0 : L = ⊥ := by
      rw [← hG, Submodule.span_eq_bot]
      intro s hs
      funext i
      exact hcon s hs i
    have h1 : (fun _ : Fin n => (1 : E)) ∈ Submodule.span E (L : Set (Fin n → E)) := hspan ▸ Submodule.mem_top
    rw [hL0, Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.mem_bot] at h1
    exact one_ne_zero (congrFun h1 ⟨0, hn⟩)
  obtain ⟨s, hsG, i, hsi⟩ := hne
  have hu : IsUnit (sp (inclE (F := F) (v.adicCompletion F) (s i))) :=
    ((isUnit_iff_ne_zero.2 hsi).map (inclE (F := F) (v.adicCompletion F))).map sp
  have ha : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ≠ 0 :=
    (hu.map (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).ne_zero
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ M (Submodule.fg_span (Set.finite_range _)) hle hjac
  have hmem : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈ M := Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact ha hmem

end

theorem local_idempotent_cases :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (g : ℕ), (g : 𝓞 F) ∈ v.asIdeal → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → 0 < n → ∀ e : E ⊗[F] v.adicCompletion F, e * e = e → e * sigR σ (v.adicCompletion F) e = 0 → (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - e - sigR σ (v.adicCompletion F) e) • y = (g : E ⊗[F] v.adicCompletion F) • z) → sp e = (1, 0) ∨ sp e = (0, 1) := by
  intro F E _ _ _ _ _ σ n v sp hsw hdiag g hg L hL hn e he heo hfull
  have hse : sp (sigR σ (v.adicCompletion F) e) = ((sp e).2, (sp e).1) := by
    rw [hsw]
    rfl
  have hidem : sp e * sp e = sp e := by rw [← map_mul, he]
  have horth : sp e * ((sp e).2, (sp e).1) = 0 := by rw [← hse, ← map_mul, heo, map_zero]
  have ha : (sp e).1 * (sp e).1 = (sp e).1 := congrArg Prod.fst hidem
  have hb : (sp e).2 * (sp e).2 = (sp e).2 := congrArg Prod.snd hidem
  have hab : (sp e).1 * (sp e).2 = 0 := congrArg Prod.fst horth
  have ha' : (sp e).1 = 0 ∨ (sp e).1 = 1 := by
    have h0 : (sp e).1 * ((sp e).1 - 1) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hb' : (sp e).2 = 0 ∨ (sp e).2 = 1 := by
    have h0 : (sp e).2 * ((sp e).2 - 1) = 0 := by rw [mul_sub, mul_one, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases ha' with ha0 | ha1 <;> rcases hb' with hb0 | hb1
  · exfalso
    have he0 : e = 0 := sp.injective (by rw [map_zero]; exact Prod.ext ha0 hb0)
    apply not_forall_loc_eq_natCast_smul v sp hdiag g hg L hL hn
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hfull y hy
    refine ⟨z, hz, ?_⟩
    rw [he0, map_zero, sub_zero, sub_zero, one_smul] at hyz
    exact hyz
  · exact Or.inr (Prod.ext ha0 hb1)
  · exact Or.inl (Prod.ext ha1 hb0)
  · exfalso
    rw [ha1, hb1, one_mul] at hab
    exact one_ne_zero hab

end GlobalTheory.St.G
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_frame_idempotent_factor_cases : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (g : ℕ), (g : 𝓞 F) ∈ v.asIdeal → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → 0 < n → ∀ e : E ⊗[F] v.adicCompletion F, e * e = e → e * sigR σ (v.adicCompletion F) e = 0 → (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - e - sigR σ (v.adicCompletion F) e) • y = (g : E ⊗[F] v.adicCompletion F) • z) → sp e = (1, 0) ∨ sp e = (0, 1) := by
  atlas_forward_decl GlobalTheory.St.G.local_idempotent_cases
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.TypePrimeProduct

theorem natPrime_not_mem_of_other (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hO : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := by
    have := hZ.map (Int.castRingHom (𝓞 F))
    simpa using this
  obtain ⟨a, b, hab⟩ := hO
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem isUnit_natCast_of_not_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∉ v.asIdeal) :
    IsUnit ((q : ℕ) : v.adicCompletionIntegers F) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hq] at h
  simpa using h

theorem main_two (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal)
    (hm : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p : ℕ) : v.adicCompletionIntegers F)}) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p * q : ℕ) : v.adicCompletionIntegers F)} ∧
      ((p * q : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hqv := natPrime_not_mem_of_other F v hp hq hpq hpv
  refine ⟨?_, ?_⟩
  · rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit (isUnit_natCast_of_not_mem F v q hqv)]
  · rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hpv

end GlobalTheory.St.G.TypePrimeProduct

open GlobalTheory.St.G.TypePrimeProduct in

theorem GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod : ∀ (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp i : ℕ) : v.adicCompletionIntegers F)} → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp 0 * gp 1 : ℕ) : v.adicCompletionIntegers F)} ∧ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∃ q : ℕ, 0 < q ∧ gp 0 * gp 1 = gp i * q := by
  intro F _ _ gp hgp hne i v hv hm
  fin_cases i
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 0) (hgp 1) hne hv hm
    exact ⟨h1, h2, gp 1, (hgp 1).pos, rfl⟩
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 1) (hgp 0) hne.symm hv hm
    rw [mul_comm (gp 0)]
    exact ⟨h1, h2, gp 0, (hgp 0).pos, rfl⟩
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformiser_product_type_primes : ∀ (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp i : ℕ) : v.adicCompletionIntegers F)} → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp 0 * gp 1 : ℕ) : v.adicCompletionIntegers F)} ∧ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∃ q : ℕ, 0 < q ∧ gp 0 * gp 1 = gp i * q := by
  atlas_forward_decl GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FirstFactorFrame

theorem res_key {R : Type} [CommRing R] [IsLocalRing R] (f : R → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, f a = 1) (a b : R)
    (h : IsLocalRing.residue R a = IsLocalRing.residue R b) : f a = f b := by
  have hm' : a - b ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  have := hadd b (a - b)
  rw [show b + (a - b) = a by ring, hm _ hm', mul_one] at this
  exact this

theorem res_surjInv {R : Type} [CommRing R] [IsLocalRing R] (x : IsLocalRing.ResidueField R) :
    IsLocalRing.residue R (Function.surjInv IsLocalRing.residue_surjective x) = x :=
  Function.surjInv_eq (f := IsLocalRing.residue R) IsLocalRing.residue_surjective x

def resChar {R : Type} [CommRing R] [IsLocalRing R] (f : R → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, f a = 1) : AddChar (IsLocalRing.ResidueField R) ℂ where
  toFun x := f (Function.surjInv IsLocalRing.residue_surjective x)
  map_zero_eq_one' := by
    rw [res_key f hadd hm _ 0 (by rw [res_surjInv, map_zero])]
    exact hm 0 (Ideal.zero_mem _)
  map_add_eq_mul' x y := by
    rw [← hadd]
    exact res_key f hadd hm _ _ (by rw [map_add, res_surjInv, res_surjInv, res_surjInv])

theorem resChar_residue {R : Type} [CommRing R] [IsLocalRing R] (f : R → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, f a = 1) (a : R) :
    resChar f hadd hm (IsLocalRing.residue R a) = f a :=
  res_key f hadd hm _ _ (res_surjInv _)

theorem afsplitIE_mem_OAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ intV E v) :
    Formalism.UG.P.afsplitIE v x ∈ OAd F E := by
  rw [(GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F E).1]
  intro w
  by_cases h : w = v
  · subst h; rw [Formalism.UG.P.afsplit_prV_IE]; exact hx
  · rw [Formalism.UG.P.afsplit_prV_IE_ne v w h]; exact zero_mem _

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (σ : E →ₐ[F] E)
  (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

theorem fst_of_sig (hsig : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) {n : ℕ}
    (e : E ⊗[F] v.adicCompletion F) (he : sp e = (1, 0)) (x : Fin n → E ⊗[F] v.adicCompletion F)
    (hx : x = sigR σ (v.adicCompletion F) e • x) (a : Fin n) : (sp (x a)).1 = 0 := by
  have h := congrFun hx a
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [h, map_mul, hsig, he]
  simp [swapR]

theorem snd_of_e {n : ℕ} (e : E ⊗[F] v.adicCompletion F) (he : sp e = (1, 0))
    (x : Fin n → E ⊗[F] v.adicCompletion F) (hx : x = e • x) (a : Fin n) : (sp (x a)).2 = 0 := by
  have h := congrFun hx a
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [h, map_mul, he]
  simp

theorem hR_snd_zero (hsig : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E ⊗[F] v.adicCompletion F) (hx : ∀ a, (sp (x a)).1 = 0) :
    (sp (hR σ J (v.adicCompletion F) x y)).2 = 0 := by
  unfold hR hform
  simp only [map_sum, map_mul, Prod.snd_sum, Prod.snd_mul, hsig]
  simp [swapR, hx]

theorem fst_mulVec {n : ℕ} (y : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (fr : GL (Fin n) (v.adicCompletion F))
    (hfr : (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1)) (j a : Fin n) :
    (sp ((y.1 *ᵥ c j) a)).1 = ∑ l, (sp (c l a)).1 *
      ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) l j := by
  have hG : fr * (fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr) =
      bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr := by group
  generalize (fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) = Mg at hG ⊢
  have hV := congrArg (fun z : GL (Fin n) (v.adicCompletion F) => (z : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a j) hG
  simp only [Units.val_mul] at hV
  rw [Matrix.mul_apply, Matrix.mul_apply] at hV
  simp only [hfr, Matrix.of_apply] at hV
  rw [hV]
  simp only [Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]
  apply Finset.sum_congr rfl
  intro d _
  simp [bc]

end Split

section Split2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}
  (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

theorem fst_dual (e : E ⊗[F] v.adicCompletion F) (he : sp e = (1, 0)) (P : Prop) [Decidable P]
    (x s : E ⊗[F] v.adicCompletion F) (c : ℕ)
    (hx : x - (if P then e else 0) = (c : E ⊗[F] v.adicCompletion F) * s) :
    (sp x).1 = (if P then 1 else 0) + (c : v.adicCompletion F) * (sp s).1 := by
  rw [sub_eq_iff_eq_add] at hx
  rw [hx, map_add, map_mul, map_natCast, Prod.fst_add, Prod.fst_mul, Prod.fst_natCast]
  split_ifs
  · rw [he]; ring
  · rw [map_zero]; simp

theorem fst_pair_sum {n : ℕ} (X : Fin n → v.adicCompletion F) (Jc : Fin n → Fin n → v.adicCompletion F)
    (B : Fin n → Fin n → v.adicCompletion F) (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (j : Fin n) :
    ∑ a, ∑ c, X a * Jc a c * (∑ l, B l c * M l j) = ∑ l, M l j * ∑ a, ∑ c, X a * Jc a c * B l c := by
  calc ∑ a, ∑ c, X a * Jc a c * (∑ l, B l c * M l j) = ∑ a, ∑ c, ∑ l, M l j * (X a * Jc a c * B l c) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ a, ∑ l, ∑ c, M l j * (X a * Jc a c * B l c) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ c, M l j * (X a * Jc a c * B l c) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end Split2

theorem local_frame_first_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (1, 0) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet t v sp hsig halg hint g hgmax L hL e he b bd hb hbd hbe hbde hdual hspan
    psi hpsi_add hpsi_int hne
  have hbd1 : ∀ i a, (sp (bd i a)).1 = 0 := fun i a => fst_of_sig cm.sig sp hsig e he (bd i) (hbde i) a
  have hb2 : ∀ j a, (sp (b j a)).2 = 0 := fun j a => snd_of_e sp e he (b j) (hbe j) a
  obtain ⟨fr, hfr, hlat⟩ := GlobalTheory.T.first_components_basis_local_lattice_split F E cm n J hJ hdet v sp hsig halg hint g hgmax L hL b (Set.range bd) hb
    (by rintro x ⟨i, rfl⟩ a; exact hbd1 i a) hspan
  have hpsi0 : psi 0 = 1 := hpsi_int 0 (zero_mem _)
  have hgF : (g : F) ≠ 0 := by
    intro h0
    obtain ⟨a, -, ha⟩ := hne
    apply ha
    rw [h0, _root_.inv_zero, map_zero, zero_mul, map_zero, hpsi0]
  set u := algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) with hu
  have hug : u * (g : E ⊗[F] v.adicCompletion F) = 1 := by
    rw [hu, ← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)), ← map_mul, inv_mul_cancel₀ hgF, map_one]
  let Fk : v.adicCompletion F → ℂ := fun x => psi (Formalism.UG.P.afsplitIE v (u * sp.symm (x, 0)))
  have hFadd : ∀ x y, Fk (x + y) = Fk x * Fk y := by
    intro x y
    simp only [Fk]
    rw [← hpsi_add, ← map_add, ← mul_add, ← map_add, Prod.mk_add_mk, add_zero]
  have hFg : ∀ w ∈ v.adicCompletionIntegers F, Fk ((g : v.adicCompletion F) * w) = 1 := by
    intro w hw
    simp only [Fk]
    have h1 : sp.symm ((g : v.adicCompletion F) * w, 0) = (g : E ⊗[F] v.adicCompletion F) * sp.symm (w, 0) := by
      apply sp.injective
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_natCast]
      ext <;> simp
    rw [h1, ← mul_assoc, hug, one_mul]
    apply hpsi_int
    apply afsplitIE_mem_OAd
    rw [hint, RingEquiv.apply_symm_apply]
    exact ⟨hw, zero_mem _⟩
  let f : v.adicCompletionIntegers F → ℂ := fun r => Fk r
  have hfadd : ∀ a b, f (a + b) = f a * f b := fun a b => by
    simp only [f]
    push_cast
    exact hFadd _ _
  have hfm : ∀ a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F), f a = 1 := by
    intro a ha
    rw [hgmax, Ideal.mem_span_singleton'] at ha
    obtain ⟨w, rfl⟩ := ha
    simp only [f]
    push_cast
    rw [mul_comm]
    exact hFg _ w.2
  refine ⟨fr, resChar f hfadd hfm, ?_, hlat, ?_⟩
  · obtain ⟨a, ha, hne'⟩ := hne
    have ha1 := ((hint a).1 ha).1
    intro h1
    apply hne'
    have h2 := resChar_residue f hfadd hfm ⟨(sp a).1, ha1⟩
    rw [h1, AddChar.one_apply] at h2
    have hea : e * a = sp.symm ((sp a).1, 0) := by
      apply sp.injective
      rw [map_mul, he, RingEquiv.apply_symm_apply]
      ext <;> simp
    rw [hea]
    exact h2.symm
  · intro y hy
    obtain ⟨hMint, hiff⟩ := GlobalTheory.T.hermitian_local_level_unitriangular_iff F E cm n J hJ hdet v sp hsig halg hint g hgmax L hL b fr hb hb2 hfr hlat t y hy
    refine ⟨hiff, fun _ => ?_⟩

    choose s hs hsd using hdual
    have hs1 : ∀ i l, (sp (s i l)).1 ∈ v.adicCompletionIntegers F := fun i l => ((hint _).1 (hs i l)).1
    have hcol := fst_mulVec sp y b fr hfr
    generalize (fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) = Mg at hMint hcol ⊢
    set M : Matrix (Fin n) (Fin n) (v.adicCompletion F) := (Mg : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hMdef
    have hform1 := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v sp hsig halg).2.2
    have hdual1 : ∀ i l, (sp (hR cm.sig J (v.adicCompletion F) (bd i) (b l))).1 =
        (if i = l then 1 else 0) + (g : v.adicCompletion F) * (sp (s i l)).1 :=
      fun i l => fst_dual sp e he (i = l) _ _ g (hsd i l)
    have hfirst : ∀ i j, (sp (hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b j))).1 =
        ∑ l, M l j * (sp (hR cm.sig J (v.adicCompletion F) (bd i) (b l))).1 := by
      intro i j
      rw [hform1]
      simp only [hform1, hcol]
      exact fst_pair_sum _ _ _ M j

    have hMj : ∀ i : Fin n, ∀ hi : i.1 + 1 < n,
        (sp (hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b ⟨i.1 + 1, hi⟩))).1 =
        M i ⟨i.1 + 1, hi⟩ + (g : v.adicCompletion F) * ∑ l, M l ⟨i.1 + 1, hi⟩ * (sp (s i l)).1 := by
      intro i hi
      rw [hfirst]
      simp only [hdual1, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by ring
    set R0 : v.adicCompletion F := ∑ i : Fin n, if hi : i.1 + 1 < n then M i ⟨i.1 + 1, hi⟩ else 0 with hR0
    set W0 : v.adicCompletion F :=
      ∑ i : Fin n, if hi : i.1 + 1 < n then ∑ l, M l ⟨i.1 + 1, hi⟩ * (sp (s i l)).1 else 0 with hW0
    have hsup : supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1 =
        sp.symm (R0 + (g : v.adicCompletion F) * W0, 0) := by
      apply sp.injective
      rw [RingEquiv.apply_symm_apply]
      unfold supSum
      rw [map_sum]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum, hR0, hW0, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · exact hMj i hi
        · simp
      · rw [Prod.snd_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        split_ifs with hi
        · exact hR_snd_zero cm.sig sp hsig J _ _ (hbd1 i)
        · simp
    have hW0i : W0 ∈ v.adicCompletionIntegers F := by
      rw [hW0]
      refine sum_mem fun i _ => ?_
      split_ifs with hi
      · exact sum_mem fun l _ => mul_mem (hMint l _) (hs1 i l)
      · exact zero_mem _
    have hr : ∀ i : Fin n, (if hi : i.1 + 1 < n then M i ⟨i.1 + 1, hi⟩ else 0) ∈ v.adicCompletionIntegers F := by
      intro i
      split_ifs
      · exact hMint _ _
      · exact zero_mem _
    have hR0i : R0 ∈ v.adicCompletionIntegers F := by
      rw [hR0]; exact sum_mem fun i _ => hr i
    have hsumres : (∑ x : Fin n, ∑ y : Fin n,
        if (x : ℕ) + 1 = y ∧ (y : ℕ) < n ∧ (y : ℕ) ≠ n then redM F v M x y else 0) =
        IsLocalRing.residue _ (⟨R0, hR0i⟩ : v.adicCompletionIntegers F) := by
      have hsub : (⟨R0, hR0i⟩ : v.adicCompletionIntegers F) = ∑ i, ⟨_, hr i⟩ := Subtype.ext (by simp [hR0])
      rw [hsub, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x.1 + 1 < n
      · rw [Finset.sum_eq_single ⟨x.1 + 1, hx⟩]
        · rw [if_pos ⟨rfl, hx, by omega⟩]
          simp only [redM, dif_pos (hMint x _)]
          congr 1
          exact Subtype.ext (by simp [hx])
        · intro y _ hy
          rw [if_neg]
          rintro ⟨h1, -, -⟩
          exact hy (Fin.ext h1.symm)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero]
        · have h0 : (⟨_, hr x⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (by simp [hx])
          rw [h0, map_zero]
        · intro y _
          rw [if_neg]
          rintro ⟨h1, h2, -⟩
          omega
    rw [hsup]
    change Fk (R0 + (g : v.adicCompletion F) * W0) = _
    rw [hFadd, hFg _ hW0i, mul_one]
    unfold lamJ
    rw [Finset.prod_range_zero, mul_one, hsumres, resChar_residue]

end GlobalTheory.St.G.FirstFactorFrame
end
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_firstFactor_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (1, 0) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  atlas_forward_decl GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory

theorem inv_upperUnitriangular (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k)
    (hlow : ∀ x y : Fin n, y < x → A x y = 0) (hdiag : ∀ x, A x x = 1) :
    (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧
      ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  have hA : A.BlockTriangular id := fun i j h => hlow i j h
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    simp [hdiag]
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (by rw [hdet]; exact isUnit_one)
  have hB : (A⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hA
  have hlowB : ∀ x y : Fin n, y < x → A⁻¹ x y = 0 := fun x y h => hB h
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hdet]; exact isUnit_one)
  have hdiagB : ∀ x, A⁻¹ x x = 1 := by
    intro x
    have h := congrFun (congrFun hmul x) x
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single x] at h
    · simpa [hdiag] using h
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [hlow x j hj, zero_mul]
      · rw [hlowB j x hj, mul_zero]
    · simp
  refine ⟨hlowB, hdiagB, ?_⟩
  intro x y hxy
  have hxy' : x < y := by
    rw [Fin.lt_def]; omega
  have h := congrFun (congrFun hmul x) y
  rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hxy'),
    Finset.sum_eq_add (x) (y) (ne_of_lt hxy')] at h
  · rw [hdiag x, hdiagB y, one_mul, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  · intro j _ hj
    rcases lt_trichotomy j x with h1 | h1 | h1
    · rw [hlow x j h1, zero_mul]
    · exact absurd h1 hj.1
    · have : y < j := by
        rcases lt_trichotomy j y with h2 | h2 | h2
        · exfalso; rw [Fin.lt_def] at h1 h2; omega
        · exact absurd h2 hj.2
        · exact h2
      rw [hlowB j y this, mul_zero]
  · simp
  · simp

end GlobalTheory
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_upperUnitriangular_superdiag_neg : ∀ (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k), (∀ x y : Fin n, y < x → A x y = 0) → (∀ x, A x x = 1) → (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧ ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  atlas_forward_decl GlobalTheory.inv_upperUnitriangular
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

namespace SecondFactor

theorem reversed_unitriangular : ∀ (k : Type) [Field k] (n : ℕ) (A M : Matrix (Fin n) (Fin n) k), (∀ x y : Fin n, ∑ l : Fin n, A (Fin.rev l) x * M l y = if x = Fin.rev y then 1 else 0) → ((((∀ x y : Fin n, y < x → A x y = 0) ∧ ∀ x, A x x = 1) ↔ ((∀ x y : Fin n, y < x → M x y = 0) ∧ ∀ x, M x x = 1)) ∧ (((∀ x y : Fin n, y < x → A x y = 0) ∧ ∀ x, A x x = 1) → ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then M x y else 0) = - ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then A x y else 0))) := by
  intro k _ n A M h
  let Ad : Matrix (Fin n) (Fin n) k := fun x y => A (Fin.rev y) (Fin.rev x)
  have hAM : Ad * M = 1 := by
    refine Matrix.ext fun x y => ?_
    rw [Matrix.mul_apply]
    have := h (Fin.rev x) y
    simp only [Ad]
    rw [this, Matrix.one_apply]
    simp only [Fin.rev_inj]
  have hMA : M * Ad = 1 := mul_eq_one_comm.1 hAM
  have hinvM : Ad⁻¹ = M := Matrix.inv_eq_right_inv hAM
  have hinvA : M⁻¹ = Ad := Matrix.inv_eq_right_inv hMA
  have hrevlt : ∀ x y : Fin n, y < x → Fin.rev x < Fin.rev y := fun x y hxy => Fin.rev_lt_rev.2 hxy
  have hAtoAd : ((∀ x y : Fin n, y < x → A x y = 0) ∧ ∀ x, A x x = 1) →
      ((∀ x y : Fin n, y < x → Ad x y = 0) ∧ ∀ x, Ad x x = 1) := fun ⟨a1, a2⟩ =>
    ⟨fun x y hxy => a1 _ _ (hrevlt x y hxy), fun x => a2 _⟩
  refine ⟨⟨fun hA => ?_, fun hM => ?_⟩, fun hA => ?_⟩
  · obtain ⟨d1, d2⟩ := hAtoAd hA
    obtain ⟨i1, i2, -⟩ := GlobalTheory.T.inv_upperUnitriangular_superdiag_neg k n Ad d1 d2
    rw [hinvM] at i1 i2
    exact ⟨i1, i2⟩
  · obtain ⟨i1, i2, -⟩ := GlobalTheory.T.inv_upperUnitriangular_superdiag_neg k n M hM.1 hM.2
    rw [hinvA] at i1 i2
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · have := i1 (Fin.rev y) (Fin.rev x) (hrevlt x y hxy)
      simpa [Ad] using this
    · have := i2 (Fin.rev x)
      simpa [Ad] using this
  · obtain ⟨d1, d2⟩ := hAtoAd hA
    obtain ⟨-, -, i3⟩ := GlobalTheory.T.inv_upperUnitriangular_superdiag_neg k n Ad d1 d2
    rw [hinvM] at i3
    have e1 : ∀ x y : Fin n, (if (x : ℕ) + 1 = y then M x y else 0) =
        - (fun p q : Fin n => if (p : ℕ) + 1 = q then A p q else 0) (Fin.rev y) (Fin.rev x) := by
      intro x y
      have hy := y.2
      have hx := x.2
      by_cases hxy : (x : ℕ) + 1 = y
      · have hc : ((Fin.rev y : Fin n) : ℕ) + 1 = (Fin.rev x : Fin n) := by
          simp only [Fin.val_rev]; omega
        simp only [if_pos hxy, if_pos hc, i3 x y hxy, Ad]
      · have hc : ¬ ((Fin.rev y : Fin n) : ℕ) + 1 = (Fin.rev x : Fin n) := by
          simp only [Fin.val_rev]; omega
        simp only [if_neg hxy, if_neg hc, neg_zero]
    simp only [e1, Finset.sum_neg_distrib]
    congr 1
    have key : ∀ f : Fin n → Fin n → k, ∑ x : Fin n, ∑ y : Fin n, f (Fin.rev y) (Fin.rev x) = ∑ x : Fin n, ∑ y : Fin n, f x y := by
      intro f
      rw [Finset.sum_comm]
      calc ∑ y : Fin n, ∑ x : Fin n, f (Fin.rev y) (Fin.rev x)
          = ∑ y : Fin n, ∑ x : Fin n, f (Fin.rev y) x :=
            Finset.sum_congr rfl fun y _ => Equiv.sum_comp Fin.revPerm (fun x => f (Fin.rev y) x)
        _ = ∑ x : Fin n, ∑ y : Fin n, f x y :=
            Equiv.sum_comp Fin.revPerm (fun y => ∑ x : Fin n, f y x)
    exact key (fun p q : Fin n => if (p : ℕ) + 1 = q then A p q else 0)

theorem reversed_relation_mod : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n g : ℕ) (A M R : Matrix (Fin n) (Fin n) (v.adicCompletion F)), (∀ a b, A a b ∈ v.adicCompletionIntegers F) → (∀ a b, M a b ∈ v.adicCompletionIntegers F) → Aᵀ * R * M = R → (∀ i j, ∃ s ∈ v.adicCompletionIntegers F, R i j - (if i = Fin.rev j then 1 else 0) = (g : v.adicCompletion F) * s) → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ x y : Fin n, ∑ l : Fin n, redM F v A (Fin.rev l) x * redM F v M l y = if x = Fin.rev y then 1 else 0 := by
  intro F _ _ v n g A M R hA hM hrel hRent hg x y
  choose s hs hs2 using hRent
  let φ : v.adicCompletionIntegers F →+* v.adicCompletion F := algebraMap _ _
  let ρ : v.adicCompletionIntegers F →+* kv F v := IsLocalRing.residue _
  let Ao : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨A a c, hA a c⟩
  let Mo : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨M a c, hM a c⟩
  let So : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨s a c, hs a c⟩
  let Ro : Fin n → Fin n → v.adicCompletionIntegers F := fun i j => (if i = Fin.rev j then 1 else 0) + (g : v.adicCompletionIntegers F) * So i j
  have hφA : ∀ a c, φ (Ao a c) = A a c := fun _ _ => rfl
  have hφM : ∀ a c, φ (Mo a c) = M a c := fun _ _ => rfl
  have hφS : ∀ a c, φ (So a c) = s a c := fun _ _ => rfl
  have hφR : ∀ i j, φ (Ro i j) = R i j := by
    intro i j
    have := hs2 i j
    have e : R i j = (if i = Fin.rev j then 1 else 0) + (g : v.adicCompletion F) * s i j := by
      rw [← this]; ring
    rw [e]
    simp only [Ro, map_add, map_mul, map_natCast, hφS]
    congr 1
    split_ifs <;> simp
  have hinj : Function.Injective φ := Subtype.val_injective
  have hE : ∑ l, (∑ p, Ao p x * Ro p l) * Mo l y = Ro x y := by
    apply hinj
    have := congrFun (congrFun hrel x) y
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    simp only [map_sum, map_mul, hφA, hφM, hφR]
    exact this
  have hg0 : ρ (g : v.adicCompletionIntegers F) = 0 := by
    refine (IsLocalRing.residue_eq_zero_iff _).2 ?_
    rw [hg]
    exact Ideal.mem_span_singleton_self _
  have hρR : ∀ i j, ρ (Ro i j) = if i = Fin.rev j then 1 else 0 := by
    intro i j
    simp only [Ro, map_add, map_mul, hg0, zero_mul, add_zero]
    split_ifs <;> simp
  have hρA : ∀ a c, ρ (Ao a c) = redM F v A a c := fun a c => (show redM F v A a c = ρ (Ao a c) from dif_pos (hA a c)).symm
  have hρM : ∀ a c, ρ (Mo a c) = redM F v M a c := fun a c => (show redM F v M a c = ρ (Mo a c) from dif_pos (hM a c)).symm
  have h := congrArg ρ hE
  simp only [map_sum, map_mul, hρR, hρA, hρM] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

theorem residue_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (0, 1) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ ψ : AddChar (kv F v) ℂ, ψ ≠ 1 ∧ ∀ (s r : v.adicCompletionIntegers F) (x : E ⊗[F] v.adicCompletion F), sp x = (0, (s : v.adicCompletion F) + (g : v.adicCompletion F) * (r : v.adicCompletion F)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * x)) = ψ (IsLocalRing.residue (v.adicCompletionIntegers F) (-s)) := by
  intro F E _ _ _ _ _ v sp halg hint g hg e he psi hadd hpsiO hne
  have hOA : ∀ x ∈ intV E v, Formalism.UG.P.afsplitIE v x ∈ OAd F E := by
    intro x hx
    refine ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 _).2 fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplit_prV_IE]; exact hx
    · rw [Formalism.UG.P.afsplit_prV_IE_ne v w hw]; exact zero_mem _
  have hpsi0 : psi 0 = 1 := hpsiO 0 (zero_mem _)
  have hgF : (g : F) ≠ 0 := by
    intro h0
    obtain ⟨a, -, ha⟩ := hne
    apply ha
    rw [h0, _root_.inv_zero, map_zero, zero_mul, map_zero, hpsi0]
  have hspA : ∀ a : F, sp (algebraMap F (E ⊗[F] v.adicCompletion F) a) =
      (algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) a) := by
    intro a
    have : algebraMap F (E ⊗[F] v.adicCompletion F) a = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [this, halg]
  set c : v.adicCompletion F := algebraMap F (v.adicCompletion F) ((g : F)⁻¹) with hc
  have hcg : c * (g : v.adicCompletion F) = 1 := by
    rw [hc, ← map_natCast (algebraMap F (v.adicCompletion F)) g, ← map_mul, inv_mul_cancel₀ hgF, map_one]
  let P : v.adicCompletion F → ℂ := fun r =>
    psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * sp.symm (0, r)))
  have hPadd : ∀ r r', P (r + r') = P r * P r' := by
    intro r r'
    have : ((0 : v.adicCompletion F), r + r') = (0, r) + (0, r') := by simp
    simp only [P]
    rw [this, map_add, mul_add, map_add, hadd]
  have hP1 : ∀ r : v.adicCompletionIntegers F, P ((g : v.adicCompletion F) * r) = 1 := by
    intro r
    have : algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * sp.symm (0, (g : v.adicCompletion F) * r) =
        sp.symm (0, (r : v.adicCompletion F)) := by
      apply sp.injective
      rw [map_mul, hspA, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      refine Prod.ext (by simp) ?_
      show c * ((g : v.adicCompletion F) * r) = r
      rw [← mul_assoc, hcg, one_mul]
    simp only [P]
    rw [this]
    refine hpsiO _ (hOA _ ((hint _).2 ?_))
    rw [RingEquiv.apply_symm_apply]
    exact ⟨zero_mem _, r.2⟩
  let Q : v.adicCompletionIntegers F → ℂ := fun u => P (-(u : v.adicCompletion F))
  have hQadd : ∀ u u', Q (u + u') = Q u * Q u' := by
    intro u u'
    simp only [Q]
    rw [← hPadd]
    congr 1
    push_cast
    ring
  have hQ1 : ∀ u ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F), Q u = 1 := by
    intro u hu
    rw [hg, Ideal.mem_span_singleton'] at hu
    obtain ⟨w, rfl⟩ := hu
    have := hP1 (-w)
    simp only [Q]
    rw [← this]
    congr 1
    push_cast
    ring
  have hsurj := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers F)
  let lift : kv F v → v.adicCompletionIntegers F := Function.surjInv hsurj
  have hlift : ∀ z, IsLocalRing.residue _ (lift z) = z := Function.surjInv_eq hsurj
  have hQres : ∀ u u', IsLocalRing.residue (v.adicCompletionIntegers F) u = IsLocalRing.residue _ u' → Q u = Q u' := by
    intro u u' h
    have hm : u - u' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
    have h2 : Q u = Q (u' + (u - u')) := by rw [add_sub_cancel]
    rw [h2, hQadd, hQ1 _ hm, mul_one]
  let ψ : AddChar (kv F v) ℂ :=
    { toFun := fun z => Q (lift z)
      map_zero_eq_one' := hQ1 _ ((IsLocalRing.residue_eq_zero_iff _).1 (hlift 0))
      map_add_eq_mul' := fun a b => by
        rw [← hQadd]
        apply hQres
        rw [map_add, hlift, hlift, hlift] }
  have hψ : ∀ u, ψ (IsLocalRing.residue _ u) = Q u := fun u => hQres _ _ (hlift _)
  refine ⟨ψ, ?_, ?_⟩
  · intro h1
    obtain ⟨a, ha, hne'⟩ := hne
    have hr := ((hint a).1 ha).2
    have he' : e * a = sp.symm (0, (sp a).2) := by
      apply sp.injective
      rw [map_mul, he, RingEquiv.apply_symm_apply]
      refine Prod.ext (by simp) (by simp)
    apply hne'
    rw [he']
    have := hψ (-⟨(sp a).2, hr⟩)
    rw [h1, AddChar.one_apply] at this
    simp only [Q] at this
    have e2 : -(((-⟨(sp a).2, hr⟩ : v.adicCompletionIntegers F)) : v.adicCompletion F) = (sp a).2 := by
      push_cast; ring
    rw [e2] at this
    exact this.symm
  · intro s r x hx
    have hxs : x = sp.symm (0, (s : v.adicCompletion F) + (g : v.adicCompletion F) * r) := by
      rw [← hx, RingEquiv.symm_apply_apply]
    rw [hψ]
    show _ = P (-((-s : v.adicCompletionIntegers F) : v.adicCompletion F))
    have e1 : -((-s : v.adicCompletionIntegers F) : v.adicCompletion F) = s := by push_cast; ring
    rw [e1, hxs]
    show P _ = _
    rw [hPadd, hP1, mul_one]

theorem inJ_full_iff {k : Type} [Field k] {n : ℕ} (t : ℕ) (X : Matrix (Fin n) (Fin n) k) :
    InJ n t n false X ↔ ((∀ x y : Fin n, y < x → X x y = 0) ∧ ∀ x, X x x = 1) := by
  have hb : ∀ x : Fin n, blkOf n t x = x := fun x => by simp [blkOf, x.2]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    exact ⟨fun x y h => h1 x y (by rw [hb, hb]; exact h), fun x => h2 x x.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun x y h => h1 x y (by rw [hb, hb] at h; exact h), fun x _ => h2 x, fun x y h => ?_, fun h => ?_⟩
    · exact absurd h (by have := y.2; omega)
    · simp at h

theorem sum_super_eq {A : Type} [AddCommMonoid A] {n : ℕ} (f : Fin n → Fin n → A) :
    (∑ i : Fin n, if hi : i.1 + 1 < n then f i ⟨i.1 + 1, hi⟩ else 0) =
      ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then f x y else 0) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.1 + 1 < n
  · rw [dif_pos hi, Finset.sum_eq_single ⟨i.1 + 1, hi⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · simp
  · rw [dif_neg hi]
    symm
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    have := y.2
    omega

end SecondFactor

open SecondFactor in

theorem local_frame_second_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (0, 1) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet t v sp hsig halg hint g hg L hL e he b bd hb hbd hbe hbde hdual hspan psi hadd hpsiO hne
  obtain ⟨sp', h1, h2⟩ : ∃ sp' : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      (∀ x, (sp' x).1 = (sp x).2) ∧ (∀ x, (sp' x).2 = (sp x).1) :=
    ⟨sp.trans RingEquiv.prodComm, fun _ => rfl, fun _ => rfl⟩
  have hsig' : ∀ x, sp' (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp' x) := by
    intro x
    refine Prod.ext ?_ ?_
    · rw [h1, hsig]; exact (h2 x).symm
    · rw [h2, hsig]; exact (h1 x).symm
  have halg' : ∀ a : v.adicCompletion F, sp' ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    refine Prod.ext ?_ ?_
    · rw [h1, halg]
    · rw [h2, halg]
  have hint' : ∀ x, x ∈ intV E v ↔ (sp' x).1 ∈ v.adicCompletionIntegers F ∧ (sp' x).2 ∈ v.adicCompletionIntegers F := by
    intro x
    rw [h1, h2, hint, and_comm]

  have hb1 : ∀ i a, (sp (b i a)).1 = 0 := by
    intro i a
    have := congrArg sp (congrFun (hbe i) a)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, he] at this
    rw [this]; simp
  have hse : sp (sigR cm.sig (v.adicCompletion F) e) = (1, 0) := by
    rw [hsig, he]; rfl
  have hbd2 : ∀ i a, (sp (bd i a)).2 = 0 := by
    intro i a
    have := congrArg sp (congrFun (hbde i) a)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hse] at this
    rw [this]; simp
  have hrange : Set.range (fun j : Fin n => bd (Fin.rev j)) = Set.range bd :=
    (Fin.revPerm.surjective.range_comp bd)
  obtain ⟨fr, hfr, hlat⟩ := GlobalTheory.T.first_components_basis_local_lattice_split F E cm n J hJ hdet v sp hsig halg hint g hg L hL
    (fun j => bd (Fin.rev j)) (Set.range b) (fun j => hbd _)
    (by rintro _ ⟨i, rfl⟩ a; exact hb1 i a)
    (by intro y hy; rw [hrange, Set.union_comm]; exact hspan y hy)
  obtain ⟨frB, hfrB, hlatB⟩ := GlobalTheory.T.first_components_basis_local_lattice_split F E cm n J hJ hdet v sp' hsig' halg' hint' g hg L hL
    b (Set.range bd) hb
    (by rintro _ ⟨i, rfl⟩ a; rw [h1]; exact hbd2 i a)
    (by intro y hy; exact hspan y hy)
  obtain ⟨ψ, hψ1, hψ⟩ := residue_character F E v sp halg hint g hg e he psi hadd hpsiO hne
  refine ⟨fr, ψ, hψ1, hlat, ?_⟩
  intro y hy
  have hA := GlobalTheory.T.hermitian_local_level_unitriangular_iff F E cm n J hJ hdet v sp' hsig' halg' hint' g hg L hL b frB hb
    (fun j a => by rw [h2]; exact hb1 j a) hfrB hlatB t y hy
  have hM := GlobalTheory.T.hermitian_local_level_unitriangular_iff F E cm n J hJ hdet v sp hsig halg hint g hg L hL
    (fun j => bd (Fin.rev j)) fr (fun j => hbd _) (fun j a => hbd2 _ a) hfr hlat t y hy
  obtain ⟨hAint, hAiff⟩ := hA
  obtain ⟨hMint, -⟩ := hM
  set Y1 : GL (Fin n) (v.adicCompletion F) := bc ((RingHom.fst _ _).comp sp.toRingHom) y with hY1
  set Y2 : GL (Fin n) (v.adicCompletion F) := bc ((RingHom.fst _ _).comp sp'.toRingHom) y with hY2
  set M : Matrix (Fin n) (Fin n) (v.adicCompletion F) := ((fr⁻¹ * Y1 * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hMdef
  set A : Matrix (Fin n) (Fin n) (v.adicCompletion F) := ((frB⁻¹ * Y2 * frB : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hAdef
  have hfM : fr.1 * M = Y1.1 * fr.1 := by
    have : fr * (fr⁻¹ * Y1 * fr) = Y1 * fr := by group
    exact congrArg Units.val this
  have hfA : frB.1 * A = Y2.1 * frB.1 := by
    have : frB * (frB⁻¹ * Y2 * frB) = Y2 * frB := by group
    exact congrArg Units.val this
  set J1 : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.of fun a c => (sp (inclE (F := F) (v.adicCompletion F) (J a c))).1 with hJ1

  have hyU : cT (sigR cm.sig (v.adicCompletion F)) y.1 * J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
      J.map (inclE (F := F) (v.adicCompletion F)) := hy.1
  have hU : Y2.1ᵀ * J1 * Y1.1 = J1 := by
    have h := congrArg (fun X => X.map ((RingHom.fst _ _).comp sp.toRingHom : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)) hyU
    simp only [Matrix.map_mul] at h
    have e1 : (cT (sigR cm.sig (v.adicCompletion F)) y.1).map ((RingHom.fst _ _).comp sp.toRingHom : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) = Y2.1ᵀ := by
      refine Matrix.ext fun a c => ?_
      show (sp (sigR cm.sig (v.adicCompletion F) (y.1 c a))).1 = (sp' (y.1 c a)).1
      rw [hsig, h1]; rfl
    rw [e1] at h
    exact h
  set R : Matrix (Fin n) (Fin n) (v.adicCompletion F) := frB.1ᵀ * J1 * fr.1 with hRdef
  have hrel : Aᵀ * R * M = R := by
    calc Aᵀ * R * M = (frB.1 * A)ᵀ * J1 * (fr.1 * M) := by
          rw [hRdef, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = frB.1ᵀ * (Y2.1ᵀ * J1 * Y1.1) * fr.1 := by
          rw [hfA, hfM, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = R := by rw [hU]

  have hpair : ∀ x w : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x w)).2 =
      ∑ a, ∑ c, (sp (x a)).1 * J1 c a * (sp (w c)).2 := by
    intro x w
    have h3 := (GlobalTheory.St.G.split_components F E cm n J hJ hdet v sp' hsig' halg').2.2 x w
    simp only [h1, h2] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    have hJac : (sp (inclE (F := F) (v.adicCompletion F) (J a c))).2 = J1 c a := by
      have hh : J a c = (cm.sig : E →+* E) (J c a) := by
        have := congrFun (congrFun hJ a) c
        exact this.symm
      have hs : inclE (F := F) (v.adicCompletion F) ((cm.sig : E →+* E) (J c a)) =
          sigR cm.sig (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (J c a)) := rfl
      rw [hh, hs, hsig]; rfl
    rw [hJac]
  have hpair1 : ∀ (i : Fin n) (w : Fin n → E ⊗[F] v.adicCompletion F), (sp (hR cm.sig J (v.adicCompletion F) (bd i) w)).1 = 0 := by
    intro i w
    rw [(GlobalTheory.St.G.split_components F E cm n J hJ hdet v sp hsig halg).2.2 (bd i) w]
    simp [hbd2]
  have hfrE : ∀ a j, fr.1 a j = (sp (bd (Fin.rev j) a)).1 := fun a j => congrFun (congrFun hfr a) j
  have hfrBE : ∀ a j, frB.1 a j = (sp (b j a)).2 := fun a j => by
    rw [← h1]; exact congrFun (congrFun hfrB a) j

  have hRw : ∀ (i : Fin n) (w : Fin n → E ⊗[F] v.adicCompletion F) (C : Fin n → v.adicCompletion F),
      (fun c => (sp (w c)).2) = frB.1 *ᵥ C →
      (sp (hR cm.sig J (v.adicCompletion F) (bd i) w)).2 = ∑ l, R l (Fin.rev i) * C l := by
    intro i w C hC
    rw [hpair]
    have hR' : ∀ l, R l (Fin.rev i) = ∑ a, ∑ c, frB.1 c l * J1 c a * (sp (bd i a)).1 := by
      intro l
      rw [hRdef, Matrix.mul_apply, Finset.sum_congr rfl fun a _ => by
        rw [Matrix.mul_apply, hfrE, Fin.rev_rev, Finset.sum_mul]]
      simp only [Matrix.transpose_apply]
    have hw : ∀ c, (sp (w c)).2 = ∑ l, frB.1 c l * C l := fun c => congrFun hC c
    simp only [hw, hR', Finset.sum_mul, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by ring
  have hRi : ∀ i j, R i j = (sp (hR cm.sig J (v.adicCompletion F) (bd (Fin.rev j)) (b i))).2 := by
    intro i j
    have := hRw (Fin.rev j) (b i) (Pi.single i 1) (by
      funext c
      simp [hfrBE])
    rw [this]
    simp [Pi.single_apply, Fin.rev_rev]
  have hg0 : ∀ x : E ⊗[F] v.adicCompletion F, (sp ((g : E ⊗[F] v.adicCompletion F) * x)).2 = (g : v.adicCompletion F) * (sp x).2 := by
    intro x
    rw [map_mul, map_natCast]; simp
  have hRent : ∀ i j, ∃ s ∈ v.adicCompletionIntegers F, R i j - (if i = Fin.rev j then 1 else 0) = (g : v.adicCompletion F) * s := by
    intro i j
    obtain ⟨s, hs, hs2⟩ := hdual (Fin.rev j) i
    refine ⟨(sp s).2, ((hint s).1 hs).2, ?_⟩
    rw [hRi, ← hg0, ← hs2, map_sub, Prod.snd_sub]
    congr 1
    by_cases hij : i = Fin.rev j
    · simp [hij, he]
    · have : ¬ Fin.rev j = i := fun h => hij h.symm
      simp [hij, this]
  have hred := reversed_relation_mod F v n g A M R hAint hMint hrel hRent hg
  obtain ⟨hiff, hsup⟩ := reversed_unitriangular (kv F v) n (redM F v A) (redM F v M) hred
  refine ⟨hAiff.trans ?_, fun hK => ?_⟩
  · rw [inJ_full_iff, inJ_full_iff]; exact hiff
  have hAu := (inJ_full_iff t _).1 (hAiff.1 hK)
  have hsupM := hsup hAu
  choose sR hsR hsR2 using hRent
  let Ao : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨A a c, hAint a c⟩
  let So : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨sR a c, hsR a c⟩
  let rr : Fin n → Fin n → v.adicCompletionIntegers F := fun i j => ∑ l, So l (Fin.rev i) * Ao l j
  let sO : v.adicCompletionIntegers F := ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then Ao x y else 0)
  let rO : v.adicCompletionIntegers F := ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then rr x y else 0)
  have hcoe : ∀ (f : Fin n → Fin n → v.adicCompletionIntegers F),
      (((∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then f x y else 0)) : v.adicCompletionIntegers F) : v.adicCompletion F) =
        ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then (f x y : v.adicCompletion F) else 0) := by
    intro f
    show algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) _ = _
    simp only [map_sum, apply_ite (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)), map_zero]
    rfl
  have hrr : ∀ i j, ((rr i j : v.adicCompletionIntegers F) : v.adicCompletion F) = ∑ l, sR l (Fin.rev i) * A l j := by
    intro i j
    show algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) _ = _
    simp only [rr, map_sum, map_mul]
    rfl
  have hterm : ∀ i j, (sp (hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b j))).2 =
      A i j + (g : v.adicCompletion F) * (rr i j : v.adicCompletion F) := by
    intro i j
    have hC : (fun c => (sp ((y.1 *ᵥ b j) c)).2) = frB.1 *ᵥ (fun l => A l j) := by
      funext c
      have e1 : (frB.1 *ᵥ (fun l => A l j)) c = (frB.1 * A) c j := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e1, hfA, Matrix.mul_apply]
      simp only [Matrix.mulVec, dotProduct]
      rw [map_sum, Prod.snd_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_mul, Prod.snd_mul, hfrBE, ← h1]
      rfl
    rw [hRw i _ _ hC, hrr, Finset.mul_sum]
    have hRl : ∀ l, R l (Fin.rev i) = (if l = i then 1 else 0) + (g : v.adicCompletion F) * sR l (Fin.rev i) := by
      intro l
      have := hsR2 l (Fin.rev i)
      rw [Fin.rev_rev] at this
      rw [← this]; ring
    simp only [hRl, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hss : sp (supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1) =
      (0, (sO : v.adicCompletion F) + (g : v.adicCompletion F) * (rO : v.adicCompletion F)) := by
    unfold supSum
    rw [map_sum]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs
      · exact hpair1 i _
      · simp
    · rw [Prod.snd_sum]
      have e1 : ∀ i : Fin n, (sp (if hi : i.1 + 1 < n then hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b ⟨i.1 + 1, hi⟩) else 0)).2 =
          if hi : i.1 + 1 < n then (fun p q => A p q + (g : v.adicCompletion F) * (rr p q : v.adicCompletion F)) i ⟨i.1 + 1, hi⟩ else 0 := by
        intro i
        split_ifs
        · exact hterm i _
        · simp
      simp only [e1]
      refine (sum_super_eq (fun p q => A p q + (g : v.adicCompletion F) * (rr p q : v.adicCompletion F))).trans ?_
      show _ = ((sO : v.adicCompletionIntegers F) : v.adicCompletion F) + (g : v.adicCompletion F) * ((rO : v.adicCompletionIntegers F) : v.adicCompletion F)
      rw [hcoe Ao, hcoe rr, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs
      · rfl
      · simp
  rw [hψ sO rO _ hss]
  have hredA : ∀ x q, redM F v A x q = IsLocalRing.residue (v.adicCompletionIntegers F) (Ao x q) := fun x q => dif_pos (hAint x q)
  have hlam : lamJ ψ (fun _ => 1) n t 0 n (redM F v M) = ψ (∑ x : Fin n, ∑ q : Fin n, (if (x : ℕ) + 1 = q then redM F v M x q else 0)) := by
    simp only [lamJ, Finset.range_zero, Finset.prod_empty, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun q _ => ?_
    have hq := q.2
    by_cases h : (x : ℕ) + 1 = q
    · rw [if_pos h, if_pos ⟨h, hq, by omega⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  rw [hlam, hsupM, map_neg]
  congr 2
  simp only [sO, map_sum, apply_ite (IsLocalRing.residue (v.adicCompletionIntegers F)), map_zero, hredA]

end GlobalTheory.St.G
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFrame_secondFactor_reversedDualBasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (0, 1) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  atlas_forward_decl GlobalTheory.St.G.local_frame_second_factor
end

section
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.frame_local_basis_unitriangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k t : ℕ) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), k = n → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, SplitsIn E (gp i)) → IsLat L → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), SelfDualAt cm.sig J v L → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, G.phi i v hv (y b) = x b) ↔ ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, (Fr.LocK L v y ↔ InJ n t n false (redM F v (G.mat i v hv fr y))) ∧ (Fr.LocK L v y → Fr.locChi v y = lamJ ψ (fun _ => 1) n t 0 n (redM F v (G.mat i v hv fr y))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet k t gp G L Fr hk hpr hne hspl hlat i v hv _hsd
  subst k
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    refine ⟨1, G.psi0 i v hv, G.psi_zero_nontrivial_character i v hv, ?_, ?_⟩
    · intro x
      exact ⟨fun _ b => b.elim0, fun _ => ⟨0, zero_mem _, fun b => b.elim0⟩⟩
    · intro y _
      refine ⟨⟨fun _ => ⟨fun x => x.elim0, fun x => x.elim0, fun x => x.elim0, fun _ x => x.elim0⟩, fun _ i => i.elim0⟩, fun _ => ?_⟩
      simp only [AdFrame.locChi, supSum, lamJ, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, map_zero,
        Finset.range_zero, Finset.prod_empty, mul_one, AddChar.map_zero_eq_one]
      exact Fr.psi_int 0 (zero_mem _)
  · obtain ⟨-, hsplitv⟩ := GlobalTheory.T.cmField_splitCompletely_place_structure F E cm (gp i) (hpr i) (hspl i)
    obtain ⟨-, hmax, -⟩ := hsplitv v hv
    obtain ⟨hmaxg, hgv, q, hq, hgq⟩ := GlobalTheory.T.uniformiser_product_type_primes F gp hpr hne i v hv hmax
    have hint := GlobalTheory.T.local_integers_iff_split_at_type_prime F E cm gp G hpr hspl i v hv
    obtain ⟨he1, he2, he3, he4, hb, hbd, hbe, hbde, hdual, hspan⟩ :=
      GlobalTheory.T.adelicLatticeFrame_component_localFrame F E cm.sig n J L (gp 0 * gp 1) n Fr v
    have hcase := GlobalTheory.T.local_frame_idempotent_factor_cases F E cm.sig n v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)
      (gp 0 * gp 1) hgv L hlat hpos _ he1 he2 he4
    have hne0 : prV (E := E) v Fr.eps ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hcase
      rcases hcase with h | h <;> simp [Prod.ext_iff] at h
    obtain ⟨a, ha, hpa⟩ := GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime F E cm Fr.psi Fr.psi_add Fr.psi_int Fr.psi_rat (gp i) (hpr i) (hspl i)
      v hv _ he3 he1 hne0
    have hnt : ∃ a ∈ intV E v, Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F)
        (((gp 0 * gp 1 : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a))) ≠ 1 := by
      refine ⟨(q : E ⊗[F] v.adicCompletion F) * a, mul_mem (natCast_mem _ q) ha, ?_⟩
      have hq0 : (q : F) ≠ 0 := by exact_mod_cast hq.ne'
      have hp0 : ((gp i : ℕ) : F) ≠ 0 := by exact_mod_cast (hpr i).ne_zero
      have key : algebraMap F (E ⊗[F] v.adicCompletion F) (((gp 0 * gp 1 : ℕ) : F)⁻¹) *
          (prV (E := E) v Fr.eps * ((q : E ⊗[F] v.adicCompletion F) * a)) =
          algebraMap F (E ⊗[F] v.adicCompletion F) (((gp i : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a) := by
        rw [← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)) q, mul_left_comm (prV (E := E) v Fr.eps),
          ← mul_assoc, ← map_mul]
        have hcast : ((gp 0 * gp 1 : ℕ) : F) = ((gp i : ℕ) : F) * (q : F) := by rw [hgq]; push_cast; ring
        congr 2
        rw [hcast]
        field_simp
      rw [key]
      exact hpa
    rcases hcase with hc | hc
    · exact GlobalTheory.T.splitPlace_firstFactor_localFrame F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
    · exact GlobalTheory.T.localFrame_secondFactor_reversedDualBasis F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
end

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeFrame_local_basis_unitriangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k t : ℕ) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), k = n → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, SplitsIn E (gp i)) → IsLat L → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), SelfDualAt cm.sig J v L → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, G.phi i v hv (y b) = x b) ↔ ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, (Fr.LocK L v y ↔ InJ n t n false (redM F v (G.mat i v hv fr y))) ∧ (Fr.LocK L v y → Fr.locChi v y = lamJ ψ (fun _ => 1) n t 0 n (redM F v (G.mat i v hv fr y))) := by
  atlas_forward_decl GlobalTheory.St.G.frame_local_basis_unitriangular
end
