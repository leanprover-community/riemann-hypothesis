import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

section
noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

private theorem constantCoeff_aeval_eq_aeval_constantCoeff {S : Type} [CommRing S] (Q : Polynomial S) (y : PowerSeries S) :
    constantCoeff (Polynomial.aeval y Q) = Polynomial.aeval (constantCoeff y) Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1

theorem cycloSimple : CycloSimpleStatement := by
  intro LL S _ _ _ _ m hm ζ E hζ hE0 hE
  have hζm : ζ ^ m = 1 := by
    obtain ⟨q, hq⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m LL
    have h := congrArg (Polynomial.aeval ζ) hq
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.1 h
  have hζu : IsUnit ζ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hmul : ζ * ζ ^ k = 1 := by rw [← pow_succ']; exact hζm
    exact ⟨⟨ζ, ζ ^ k, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩
  set Φ := Polynomial.cyclotomic m LL with hΦ
  have hsep : Φ.Separable :=
    (Polynomial.X_pow_sub_one_separable_iff.2 (by exact_mod_cast hm.ne')).of_dvd
      (Polynomial.cyclotomic.dvd_X_pow_sub_one m LL)
  obtain ⟨a, b, hab⟩ := hsep
  have hu : IsUnit (Polynomial.aeval ζ (Polynomial.derivative Φ)) := by
    have h := congrArg (Polynomial.aeval ζ) hab
    simp only [map_add, map_mul, map_one, hζ, mul_zero, zero_add] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  set y : PowerSeries S := C ζ * E with hy
  have hy0 : constantCoeff y = ζ := by simp [hy, hE0]
  have hyd : derivative S y = y := by
    simp [hy, Derivation.leibniz, derivative_C, hE, smul_eq_mul]
  have hF : Polynomial.aeval y Φ = Polynomial.aeval y (Φ.map (algebraMap LL S)) :=
    (Polynomial.aeval_map_algebraMap S y Φ).symm
  have h0 : constantCoeff (Polynomial.aeval y Φ) = 0 := by
    rw [hF, constantCoeff_aeval_eq_aeval_constantCoeff, hy0, Polynomial.aeval_map_algebraMap, hζ]
  have h1 : constantCoeff (derivative S (Polynomial.aeval y Φ)) =
      Polynomial.aeval ζ (Polynomial.derivative Φ) * ζ := by
    rw [hF, Derivation.map_aeval, hyd, smul_eq_mul, map_mul, constantCoeff_aeval_eq_aeval_constantCoeff, hy0,
      Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
  obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.2 h0
  have hGc : constantCoeff (derivative S (Polynomial.aeval y Φ)) = constantCoeff G := by
    rw [hG]
    simp [Derivation.leibniz, derivative_X, smul_eq_mul]
  have hGu : IsUnit G := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← hGc, h1]
    exact hu.mul hζu
  refine ⟨hGu.unit, ?_⟩
  rw [IsUnit.unit_spec, hG, mul_comm]

end LevelStatements.Lv
end
end

section
noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem cycloDist : CycloDistStatement := by
  unfold CycloDistStatement
  intro O _ _ l s hl hlm
  haveI : Fact l.Prime := ⟨hl⟩
  have hE := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt (p := l) s
  have hXmon : (Polynomial.X + 1 : Polynomial ℤ).Monic := by
    simpa using Polynomial.monic_X_add_C (1 : ℤ)
  have hXdeg : (Polynomial.X + 1 : Polynomial ℤ).natDegree ≠ 0 := by
    rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]; exact one_ne_zero
  have hPmon : ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).Monic :=
    (Polynomial.cyclotomic.monic _ ℤ).comp hXmon hXdeg
  have hQ : (Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) =
      ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).map (Int.castRingHom O) := by
    simp [Polynomial.map_comp]
  rw [hQ]
  refine { mem := fun {n} hn => ?_, monic := hPmon.map _ }
  rw [hPmon.natDegree_map] at hn
  rw [Polynomial.coeff_map]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hE.mem hn)
  rw [← ha, smul_eq_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (by simpa using hlm)

end LevelStatements.Lv
end
end

section
noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem piSeries : PiSeriesStatement := by
  intro LL ι _
  refine ⟨fun f => ?_, fun F => ⟨fun k => ?_, ?_⟩⟩
  · refine ⟨PowerSeries.mk fun n i => coeff n (f i), fun i => ?_, fun G hG => ?_⟩
    · ext n
      simp [coeff_map]
    · ext n i
      rw [coeff_mk, ← hG i, coeff_map]
      rfl
  · simp only [X_pow_dvd_iff, coeff_map]
    constructor
    · intro h i d hd
      rw [h d hd]
      rfl
    · intro h d hd
      funext i
      exact h i d hd
  · rw [isUnit_iff_constantCoeff, Pi.isUnit_iff]
    refine forall_congr' fun i => ?_
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      coeff_map]
    rfl

end LevelStatements.Lv
end
end

section
noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

def ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) :
    PowerSeries (ι → LL) :=
  PowerSeries.mk fun n i => coeff n (f i)

theorem map_evalRingHom_ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) (i : ι) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (ofPiFamily f) = f i := by
  ext n
  simp [ofPiFamily, PowerSeries.coeff_map, PowerSeries.coeff_mk]

theorem ext_evalRingHom {LL ι : Type} [CommRing LL] {F G : PowerSeries (ι → LL)}
    (h : ∀ i, PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F =
      PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) : F = G := by
  ext n i
  have h' : coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F) =
      coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) := by rw [h i]
  simpa [PowerSeries.coeff_map] using h'

def piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) : PowerSeries O →ₐ[O] PowerSeries (ι → LL) where
  toFun a := ofPiFamily fun i => ρ i a
  map_one' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_mul' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_zero' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_add' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  commutes' c := ext_evalRingHom fun i => by
    rw [map_evalRingHom_ofPiFamily, AlgHom.commutes]
    ext n
    simp [PowerSeries.algebraMap_apply, coeff_C]

theorem map_evalRingHom_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (piAlgHom ρ a) = ρ i a := by
  first
    | exact map_evalRingHom_ofPiFamily (fun i => ρ i a) i
    | (simp only [piAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
       exact map_evalRingHom_ofPiFamily _ i)

theorem constantCoeff_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    constantCoeff (piAlgHom ρ a) i = constantCoeff (ρ i a) := by
  rw [← map_evalRingHom_piAlgHom ρ i a, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  rfl

theorem cyclotomic_comp_dvd {LL : Type} [Field LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n) (r : Polynomial LL)
    (hr : ∀ ζ, IsPrimitiveRoot ζ n → r.eval (ζ - 1) = 0) :
    (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) ∣ r := by
  classical
  have hdiv : Polynomial.cyclotomic n LL ∣ r.comp (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ₀]
    apply Finset.prod_dvd_of_coprime
    · exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _
    · intro μ hμ
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_comp]
      simpa using hr μ ((mem_primitiveRoots hn).mp hμ)
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c.comp (Polynomial.X + 1), ?_⟩
  have hback : (r.comp (Polynomial.X - 1)).comp (Polynomial.X + 1) = r := by
    rw [Polynomial.comp_assoc]
    simp
  rw [← hback, hc, Polynomial.mul_comp]

private theorem derivative_exp_eq_exp' (A : Type) [Field A] [CharZero A] :
    derivative A (PowerSeries.exp A) = PowerSeries.exp A := by
  ext n
  have key : (1 / ((n + 1).factorial : ℚ)) * ((n : ℚ) + 1) = 1 / (n.factorial : ℚ) := by
    have h0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_exp, PowerSeries.coeff_exp]
  have h := congrArg (algebraMap ℚ A) key
  rw [map_mul] at h
  simpa using h

private theorem constantCoeff_exp_eq_one (A : Type) [Field A] [CharZero A] :
    constantCoeff (PowerSeries.exp A) = 1 := by
  first
    | simp
    | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_exp]; simp)

private theorem cyclotomic_comp_pow_dvd_of_X_pow_dvd {O LL : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field LL] [CharZero LL]
    [Algebra O LL] [IsFractionRing O LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hP : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).IsDistinguishedAt (maximalIdeal O))
    (ρ : LL → (PowerSeries O →ₐ[O] PowerSeries LL))
    (hρ : ∀ ζ, IsPrimitiveRoot ζ n → 1 + ρ ζ X = C ζ * PowerSeries.exp LL)
    (k : ℕ) (a : PowerSeries O)
    (hk : ∀ ζ, IsPrimitiveRoot ζ n → (X : PowerSeries LL) ^ k ∣ ρ ζ a) :
    (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) ^ k ∣ a := by
  classical
  have hexp0 := constantCoeff_exp_eq_one LL
  have hcyc : ∀ z : PowerSeries LL, Polynomial.aeval z (Polynomial.cyclotomic n O) =
      Polynomial.aeval z (Polynomial.cyclotomic n LL) := by
    intro z
    first
      | rw [← Polynomial.map_cyclotomic n (algebraMap O LL), Polynomial.aeval_map_algebraMap]
      | rw [← Polynomial.map_cyclotomic_int n O, ← Polynomial.map_cyclotomic_int n LL,
          ← algebraMap_int_eq, ← algebraMap_int_eq, Polynomial.aeval_map_algebraMap,
          Polynomial.aeval_map_algebraMap]
  have hunit : ∀ ζ, IsPrimitiveRoot ζ n → ∃ w : (PowerSeries LL)ˣ,
      ρ ζ (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (w : PowerSeries LL) * X := by
    intro ζ hζ
    have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic n LL) = 0 := by
      rw [Polynomial.coe_aeval_eq_eval]
      haveI : NeZero (n : LL) := ⟨by exact_mod_cast hn.ne'⟩
      first
        | exact Polynomial.isRoot_cyclotomic_iff.mpr hζ
        | exact Polynomial.isRoot_cyclotomic hn hζ
    obtain ⟨w, hw⟩ := cycloSimple LL LL n hn ζ (PowerSeries.exp LL) hroot hexp0
      (derivative_exp_eq_exp' LL)
    refine ⟨w, ?_⟩
    rw [algHom_coe_eq_aeval, Polynomial.aeval_comp]
    have h1 : Polynomial.aeval (ρ ζ X) (Polynomial.X + 1 : Polynomial O) =
        C ζ * PowerSeries.exp LL := by
      rw [map_add, Polynomial.aeval_X, map_one, add_comm]
      exact hρ ζ hζ
    rw [h1, hcyc]
    exact hw
  choose! w hw using hunit
  have hWu : IsUnit (ofPiFamily fun i : {ζ : LL // IsPrimitiveRoot ζ n} => (w i.1 : PowerSeries LL)) :=
    ((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).2.mpr fun i => by
      rw [map_evalRingHom_ofPiFamily]
      exact (w i.1).isUnit
  have hρP : piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1)
      (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (hWu.unit : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) * X := by
    rw [IsUnit.unit_spec]
    apply ext_evalRingHom
    intro i
    rw [map_evalRingHom_piAlgHom, map_mul, map_evalRingHom_ofPiFamily, PowerSeries.map_X]
    exact hw i.1 i.2
  have hcc : ∀ i : {ζ : LL // IsPrimitiveRoot ζ n},
      constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) i = i.1 - 1 := by
    intro i
    rw [constantCoeff_piAlgHom]
    have h : constantCoeff (1 + ρ i.1 X) = constantCoeff (C i.1 * PowerSeries.exp LL) := by
      rw [hρ i.1 i.2]
    rw [map_add, map_one, map_mul, constantCoeff_C, hexp0, mul_one] at h
    linear_combination h
  have hroots : ∀ r : Polynomial LL,
      Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r = 0 →
        ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) ∣ r := by
    intro r hr
    have hmap : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) =
        (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) := by
      rw [Polynomial.map_comp, Polynomial.map_cyclotomic, Polynomial.map_add, Polynomial.map_X,
        Polynomial.map_one]
    rw [hmap]
    apply cyclotomic_comp_dvd n hn ζ₀ hζ₀ r
    intro ζ hζ
    have h : (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ = 0 := by
      rw [hr]
      rfl
    rw [show (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ =
        Polynomial.aeval (constantCoeff (piAlgHom
          (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) ⟨ζ, hζ⟩) r from
        (Polynomial.aeval_algHom_apply (Pi.evalAlgHom LL (fun _ : {ζ : LL // IsPrimitiveRoot ζ n} => LL)
          ⟨ζ, hζ⟩) _ r).symm, hcc, Polynomial.coe_aeval_eq_eval] at h
    exact h
  have hXk : (X : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) ^ k ∣
      piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) a :=
    (((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).1 k).mpr fun i => by
      rw [map_evalRingHom_piAlgHom]
      exact hk i.1 i.2
  exact rhoCompl O LL ({ζ : LL // IsPrimitiveRoot ζ n} → LL) _ hP
    (piAlgHom fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) ⟨hWu.unit, hρP⟩ hroots k a hXk

theorem splitCompl : SplitComplStatement := by
  unfold SplitComplStatement
  intro O LL _ _ _ _ _ _ _ _ l s hl hlm hζ0 ρ hρ k a hk
  obtain ⟨ζ₀, hζ₀⟩ := hζ0
  exact cyclotomic_comp_pow_dvd_of_X_pow_dvd (l ^ (s + 1)) (pow_pos hl.pos _) ζ₀ hζ₀
    (cycloDist O l s hl hlm) ρ hρ k a hk

end LevelStatements.Lv
end
end
