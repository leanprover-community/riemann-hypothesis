import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta

section
open Formalism.Per6 in
private theorem exists_finset_adjoin_laurent_preimage {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (x : Loc2 a t) : ∃ (k : ℕ) (y : A), Loc2.mk₀ a t t ^ k * x = Loc2.mk₀ a t y := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj
    (algebraMap A (Localization.Away a) t) (S := Localization.Away (algebraMap A (Localization.Away a) t)) x
  obtain ⟨m, y, hy⟩ := IsLocalization.Away.surj a (S := Localization.Away a) b
  have hb' : x * Loc2.mk₀ a t t ^ n = Loc2.mk₁ a t b := hb
  have hy' : Loc2.mk₁ a t b * Loc2.mk₀ a t a ^ m = Loc2.mk₀ a t y := by
    have := congrArg (Loc2.mk₁ a t) hy
    simpa [Loc2.mk₀] using this
  refine ⟨r * m + n, y * c ^ m, ?_⟩
  have hT : Loc2.mk₀ a t t ^ r = Loc2.mk₀ a t a * Loc2.mk₀ a t c := by
    rw [← map_pow, hc, map_mul]
  rw [map_mul, map_pow, ← hy', ← hb', pow_add, pow_mul, hT, mul_pow]
  ring

open Formalism.Per6 in
private theorem exists_pow_kill_of_localization_zero {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (y : A) (hy : Loc2.mk₀ a t y = 0) : ∃ k : ℕ, t ^ k * y = 0 := by
  have h1 : algebraMap (Localization.Away a) (Localization.Away (algebraMap A (Localization.Away a) t))
      (algebraMap A (Localization.Away a) y) = 0 := hy
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap A (Localization.Away a) t)) _ _).1 h1
  have h2 : algebraMap A (Localization.Away a) (t ^ k * y) = 0 := by
    simpa [map_mul, map_pow] using hk
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).1 h2
  refine ⟨r * m + k, ?_⟩
  have hm' : a ^ m * (t ^ k * y) = 0 := hm
  calc t ^ (r * m + k) * y = c ^ m * (a ^ m * (t ^ k * y)) := by
        rw [pow_add, pow_mul, hc, mul_pow]; ring
    _ = 0 := by rw [hm', mul_zero]

theorem UpperTheory.Gal.crystallineComparison.Br.locFacts :
    UpperTheory.Gal.crystallineComparison.Br.LocFacts := by
  intro A _ a t ⟨r, c, hc⟩
  exact ⟨exists_finset_adjoin_laurent_preimage a t c r hc, exists_pow_kill_of_localization_zero a t c r hc⟩
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem cp_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[l] →+* ℂ_[l]) = galCp τ :=
  RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]) x

private theorem ainf_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (cp_eq σ τ h) _ _

private theorem away_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galAway σ = ACris.galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, ainf_eq σ τ h])

private theorem cris_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galCris σ = ACris.galCris τ := by
  have e : ACris.galZero σ = ACris.galZero τ := RingHom.ext fun y => Subtype.ext (by
    rw [ACris.coe_galZero, ACris.coe_galZero, away_eq σ τ h])
  rw [ACris.galCris, ACris.galCris, e]

theorem actEq : ActEq := by
  intro l _
  refine ⟨fun K g x => ?_, fun z => ?_⟩
  · exact RingHom.congr_fun (cris_eq _ _ fun _ => rfl) x
  · have h : (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)).comp ((Formalism.Per6.ainfMap l).comp (Formalism.Per6.zA l)) = zA l :=
      ringHom_ext_padicInt _ _
    exact congrArg (Formalism.Per6.cB l) (RingHom.congr_fun h z)

end UpperTheory.Gal.crystallineComparison.Br
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison GroundTheory.PAdicHodge

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem l_dvd : ∃ r : ℕ, (l : Acris l) ∣ tA l ^ r := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1
    (ACris.periodT_pow_mem' (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l)))
  exact ⟨l - 1, u, by rw [tA, ← hu, mul_comm]⟩

private def cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : Acris l →+* P.R.B :=
  T.eB.symm.toRingHom.comp (Formalism.Per6.cB l)

private theorem eB_cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    T.eB (cT T a) = Formalism.Per6.cB l a :=
  T.eB.apply_symm_apply _

private theorem cT_unit {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : IsUnit (cT T (tA l)) :=
  (Formalism.Per6.Loc2.isUnit_right (l : Acris l) (tA l)).map T.eB.symm

private theorem cT_loc {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : P.R.B) :
    ∃ (r : ℕ) (a : Acris l), cT T (tA l) ^ r * x = cT T a := by
  obtain ⟨r, y, h⟩ := (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).1 (T.eB x)
  refine ⟨r, y, T.eB.injective ?_⟩
  rw [map_mul, map_pow, eB_cT, eB_cT]
  exact h

private theorem cT_ker {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l)
    (h : cT T a = 0) : ∃ r : ℕ, tA l ^ r * a = 0 := by
  refine (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).2 a ?_
  have h1 := eB_cT T a
  rw [h, map_zero] at h1
  exact h1.symm

private theorem cT_φ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    P.φB (cT T a) = cT T (phiA l a) := by
  refine T.eB.injective ?_
  rw [T.frob, eB_cT, eB_cT]
  exact PositivityTheory.LocInh.φB_cB a

private theorem cT_σ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (a : Acris l) :
    P.actQ g.1 (cT T a) = cT T (galA g a) := by
  refine T.eB.injective ?_
  rw [T.actB, eB_cT, eB_cT, ((actEq l).1 K g a)]
  exact PositivityTheory.LocInh.σB_cB _ a

private theorem algebraMap_padic_int_eq_period {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : ℤ_[l]) :
    algebraMap ℚ_[l] P.R.B (x : ℚ_[l]) = cT T (zA l x) := by
  refine T.eB.injective ?_
  rw [T.zB, eB_cT]
  exact (actEq l).2 x

private def pullbackToFiniteExtension {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) : PB l K.1 where
  C := P.R.B
  c := cT T
  φ := P.φB
  σ g := (P.actQ g.1).toAlgHom
  t_unit := cT_unit T
  loc := cT_loc T
  ker := cT_ker T
  φ_c := cT_φ T
  σ_c := cT_σ T K.1
  z_c := algebraMap_padic_int_eq_period T

theorem pBTied : PBTied := by
  intro l _ P AI hT K
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  exact ⟨pullbackToFiniteExtension T K, AlgEquiv.refl, fun _ _ => rfl, fun _ => rfl, PositivityTheory.LocInh.tiedA_φ_injective P⟩

end UpperTheory.Gal.crystallineComparison.Br
end
end

section
noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison.Br

theorem annDrop : AnnDrop := by
  intro F G B C _ _ _ _ _ _ σ φ s ψ e hσ hφ hψ V _ _ V₀ _ _ i act ρ hρ f q n N A T hT hrel x hx
  rw [mem_Dinv] at hx
  have hpow : ∀ (m : ℕ) (b : B), e ((φ.toLinearMap ^ m) b) = (ψ.toLinearMap ^ m) (e b) := by
    intro m
    induction m with
    | zero => intro b; simp
    | succ m ih =>
      intro b
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact hφ _
  let Φ : V₀ ⊗[F] B ≃ₗ[F] V ⊗[F] C := TensorProduct.congr i.symm e.toLinearEquiv
  have hcomm : ∀ (a : End F V₀) (a' : End F V) (b : End F B) (b' : End F C),
      (∀ v, i.symm (a v) = a' (i.symm v)) → (∀ y, e (b y) = b' (e y)) →
      ∀ z, Φ (AlgebraTensorModule.map a b z) = TensorProduct.map a' b' (Φ z) := by
    intro a a' b b' ha hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v y =>
      simp only [Φ, AlgebraTensorModule.map_tmul, TensorProduct.congr_tmul, TensorProduct.map_tmul]
      rw [ha v]
      congr 1
      exact hb y
    | add u w hu hw => simp only [map_add, hu, hw]
  have hinv : ∀ g, TensorProduct.map (act g) (s g).toLinearMap (Φ x) = Φ x := by
    intro g
    rw [← hcomm (ρ g) (act g) (σ g) (s g).toLinearMap ?_ (hσ g) x, hx g]
    intro v
    have h := hρ g (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  have hsum := hrel (Φ x) hinv
  have hinj : Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (ψ.toLinearMap ^ (f * N))) := by
    have h0 : Function.Injective (ψ.toLinearMap ^ (f * N)) := by
      rw [Module.End.coe_pow]
      exact Function.Injective.iterate hψ _
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h0
  have hz : ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) •
      TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j))) (Φ x) = 0 := by
    apply hinj
    rw [map_zero, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, ← Module.End.mul_eq_comp,
      ← pow_add]
    congr 3
    ring
  apply Φ.injective
  rw [map_zero, map_sum, Finset.sum_range, ← hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [hcomm (T j) (A j) ((φ.toLinearMap ^ f) ^ (n - (j : ℕ))) (ψ.toLinearMap ^ (f * (n - j))) ?_ ?_ x]
  · intro v
    have h := hT j (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  · intro y
    rw [← pow_mul]
    exact hpow _ y

end UpperTheory.Gal.crystallineComparison.Br
end
end

section
theorem UpperTheory.Gal.crystallineComparison.Br.annModel :
    UpperTheory.Gal.crystallineComparison.Br.AnnModel := by
  intro hF l _ P AI hT K _ _ f hf hc ϖ hϖ M hM n j T hr hP A hA V₀ _ _ i ρ hρ T₀ hT₀
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨B, e, heσ, heφ, hinj⟩ := UpperTheory.Gal.crystallineComparison.Br.pBTied l P AI hT K
  obtain ⟨N, hN⟩ := hF l K.1 f hf hc ϖ hϖ M hM n j T hr hP A hA B
  exact UpperTheory.Gal.crystallineComparison.Br.annDrop ℚ_[l] _ _ _ (UpperTheory.Gal.crystallineComparison.σCr P K) P.φB B.σ B.φ e heσ heφ hinj
    (M.V j) V₀ i (fun g => M.act j g) ρ hρ f (l ^ f) n N A T₀ hT₀ hN
end
