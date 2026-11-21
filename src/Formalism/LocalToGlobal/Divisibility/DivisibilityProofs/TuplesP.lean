import Mathlib
import Formalism.LocalToGlobal.Divisibility.TuplesLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors

namespace Formalism.L2.DIV


section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tensor_conjugation_tmul (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) (r : R) :
    sigR σ R (e ⊗ₜ[F] r) = σ e ⊗ₜ[F] r := by
  rfl

theorem conjugation_involutive (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    sigR σ R (sigR σ R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e r => rw [tensor_conjugation_tmul, tensor_conjugation_tmul, hσ.2.1]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem add_conjugation_mem_range (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    z + sigR σ R z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e r =>
    obtain ⟨a, ha⟩ := hσ.2.2 (e + σ e) (by rw [map_add, hσ.2.1, add_comm])
    refine ⟨a • r, ?_⟩
    show (1 : E) ⊗ₜ[F] (a • r) = e ⊗ₜ[F] r + sigR σ R (e ⊗ₜ[F] r)
    rw [tensor_conjugation_tmul, ← TensorProduct.add_tmul, ← ha, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    have : x + y + sigR σ R (x + y) = (x + sigR σ R x) + (y + sigR σ R y) := by rw [map_add]; ring
    rw [this]; exact add_mem hx hy

theorem conjugation_fixed_mem_range [CharZero F] (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R]
    (z : E ⊗[F] R) (hz : sigR σ R z = z) :
    z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by
  have h := add_conjugation_mem_range σ hσ R z
  rw [hz] at h
  have h2 : z = (2⁻¹ : F) • (z + z) := by
    rw [← two_smul F z, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  rw [h2]; exact Subalgebra.smul_mem _ h _

theorem include_right_injective_of_field (R : Type) [CommRing R] [Algebra F R] :
    Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective



end Gen

theorem unitary_det_norm_one {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (hJ : IsUnit J.det)
    (g : GL (Fin n) A) (hg : g ∈ UJ σ J) : σ (g : Matrix (Fin n) (Fin n) A).det * (g : Matrix (Fin n) (Fin n) A).det = 1 := by
  have h : cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, cT, Matrix.det_transpose] at h2
  have h3 : ((g : Matrix (Fin n) (Fin n) A).map σ).det = σ (g : Matrix (Fin n) (Fin n) A).det := by
    rw [RingHom.map_det]; rfl
  rw [h3] at h2
  apply hJ.mul_left_cancel
  linear_combination h2

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conjugation_units_val (σ : E →ₐ[F] E) (x : (AfE F E)ˣ) :
    ((conjId σ x : (AfE F E)ˣ) : AfE F E) = sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) := rfl

theorem idele_conjugation_involutive (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (x : (AfE F E)ˣ) : conjId σ (conjId σ x) = x := by
  apply Units.ext
  rw [conjugation_units_val, conjugation_units_val, conjugation_involutive σ hσ]

theorem mem_ker_norm_quotient_iff (σ : E →ₐ[F] E) (x : (AfE F E)ˣ) : x ∈ (h90 σ).ker ↔ conjId σ x = x := by
  rw [MonoidHom.mem_ker, h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_one, eq_comm]


end Main

theorem fixed_field_is_base : FixedIsIdF := by
  intro F E _ _ _ _ _ σ hσ
  ext x
  rw [mem_ker_norm_quotient_iff]
  constructor
  · intro hx
    have h1 : sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = x := by
      rw [← conjugation_units_val, hx]
    have h2 : sigR σ (FiniteAdeleRing (𝓞 F) F) ((x⁻¹ : (AfE F E)ˣ) : AfE F E) = ((x⁻¹ : (AfE F E)ˣ) : AfE F E) := by
      rw [← conjugation_units_val, map_inv, hx]
    obtain ⟨r, hr⟩ := conjugation_fixed_mem_range σ hσ _ _ h1
    obtain ⟨s, hs⟩ := conjugation_fixed_mem_range σ hσ _ _ h2
    have hrs : r * s = 1 := by
      apply include_right_injective_of_field (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      rw [map_mul, map_one]
      erw [hr, hs]
      exact x.mul_inv
    refine ⟨⟨r, s, hrs, by rw [mul_comm]; exact hrs⟩, ?_⟩
    apply Units.ext
    exact hr
  · rintro ⟨r, rfl⟩
    apply Units.ext
    rw [conjugation_units_val]
    show sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (r : FiniteAdeleRing (𝓞 F) F)) = (1 : E) ⊗ₜ[F] (r : FiniteAdeleRing (𝓞 F) F)
    rw [tensor_conjugation_tmul, map_one]

theorem conjugation_invariant_measure : ConjInv := by
  intro F E _ _ _ _ _ L _ σ ξ hσ hξ
  ext1 x
  rw [MonoidHom.comp_apply, MonoidHom.inv_apply, eq_inv_iff_mul_eq_one, ← map_mul]
  have : conjId σ x * x ∈ (h90 σ).ker := by
    rw [mem_ker_norm_quotient_iff, map_mul, idele_conjugation_involutive σ hσ, mul_comm]
  rw [fixed_field_is_base F E σ hσ] at this
  exact hξ this

theorem det_in_unitary_one : DetInUnitaryOne := by
  intro F E _ _ _ _ _ σ n J hJ g hg
  have hJ' : IsUnit (J.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))).det := by
    have : (J.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))).det =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) J.det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hJ.map _
  have h := unitary_det_norm_one _ _ hJ' g hg
  rw [U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply]
  apply Units.ext
  rw [Units.val_mul, conjugation_units_val, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact h





section A2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F







end A2




section C

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def c_lat (x : (AfE F E)ˣ) : Submodule (𝓞 E) E where
  carrier := {e | ((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE e ∈ RInt F E}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add, mul_add] at *
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul, mul_left_comm]
    exact mul_mem (Formalism.UG.CS.incl_int c) ha




def integralAdeleSpan (N : Submodule (𝓞 E) E) : Submodule (RInt F E) (AfE F E) :=
  Submodule.span (RInt F E) (ιE '' (N : Set E))






end C



section B

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bEps (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : RInt F E :=
  ⟨afsplitEps E v, afsplit_eps_int v⟩

theorem b_eps_idem (v : HeightOneSpectrum (𝓞 F)) : bEps E v * bEps E v = bEps E v :=
  Subtype.ext (afsplit_eps_idem v)

theorem b_toRInt_val (b : 𝓞 E) :
    ((toRInt F E b : RInt F E) : AfE F E) = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E b) := rfl

theorem b_toRInt_alg (d : 𝓞 F) :
    ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) d) : RInt F E) : AfE F E) =
      (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d := by
  rw [b_toRInt_val, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, adelstab_incl_C]
  rfl

theorem b_eps_val (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F) := by
  rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]

theorem b_mem_suppAt (v : HeightOneSpectrum (𝓞 F)) (x : (AfE F E)ˣ) :
    x ∈ suppAt E v ↔ ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → prV (E := E) v' (x : AfE F E) = 1 := by
  simp only [suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem b_eps_mul (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E)
    (hz : ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → prV (E := E) v' z = 0) : afsplitEps E v * z = z := by
  rw [← sub_eq_zero]
  apply afsplit_inj
  intro w
  by_cases h : w = v
  · subst h
    rw [map_sub, map_mul, afsplit_prV_eps, one_mul, sub_self]
  · rw [map_sub, map_mul, hz w h, mul_zero, sub_self]

theorem b_eps_mul_unit (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    bEps E v * ((u : RInt F E) - 1) = (u : RInt F E) - 1 := by
  apply Subtype.ext
  apply b_eps_mul v
  intro v' hv'
  have := (b_mem_suppAt v _).mp hu v' hv'
  show prV (E := E) v' (((u : RInt F E) : AfE F E) - 1) = 0
  rw [map_sub, map_one, sub_eq_zero]
  exact this

theorem b_val_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), levelaf_valued_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact hr

theorem b_inv_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, b_val_one v r hr, inv_one]

theorem b_alg_ne_zero (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ≠ 0 := by
  intro h
  have := b_val_one v r hr
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem b_loc_inv (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    ∃ ρ : RInt F E, toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ρ = bEps E v := by
  refine ⟨⟨(1 : E) ⊗ₜ[F] afsplitI v (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹, ?_⟩, ?_⟩
  · have := levelaf_tmul_mem (F := F) (E := E) 1 (afsplitI_mem_intAd v _ (b_inv_int v r hr))
    rwa [map_one] at this
  · apply Subtype.ext
    show ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) : RInt F E) : AfE F E) * _ = afsplitEps E v
    rw [b_toRInt_alg, Algebra.TensorProduct.tmul_mul_tmul, one_mul, b_eps_val]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    by_cases h : w = v
    · subst h
      rw [afsplit_mul_apply, afsplitI_self, afsplitI_self]
      exact mul_inv_cancel₀ (b_alg_ne_zero w r hr)
    · rw [afsplit_mul_apply, afsplitI_ne v w h, afsplitI_ne v w h, mul_zero]

theorem b_off_inv (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F)
    (hr : ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → r ∉ v'.asIdeal) :
    ∃ ρ : RInt F E, toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ρ = 1 - bEps E v := by
  classical
  have hint : ∀ w : HeightOneSpectrum (𝓞 F),
      (if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹) ∈
        w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact zero_mem _
    · exact b_inv_int w r (hr w h)
  let a : FiniteAdeleRing (𝓞 F) F :=
    ⟨fun w => if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹,
      Filter.Eventually.of_forall hint⟩
  have ha : a ∈ intAd F := hint
  refine ⟨⟨(1 : E) ⊗ₜ[F] a, ?_⟩, ?_⟩
  · have := levelaf_tmul_mem (F := F) (E := E) 1 ha
    rwa [map_one] at this
  · apply Subtype.ext
    show ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) : RInt F E) : AfE F E) * _ = 1 - afsplitEps E v
    rw [b_toRInt_alg, Algebra.TensorProduct.tmul_mul_tmul, one_mul, b_eps_val, Algebra.TensorProduct.one_def,
      ← TensorProduct.tmul_sub]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    rw [afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply]
    show algebraMap (𝓞 F) (w.adicCompletion F) r *
      (if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹) = _
    by_cases h : w = v
    · subst h
      rw [if_pos rfl, afsplitI_self, mul_zero, sub_self]
    · rw [if_neg h, afsplitI_ne v w h, sub_zero]
      exact mul_inv_cancel₀ (b_alg_ne_zero w r (hr w h))

theorem b_pi (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, π ∈ v.asIdeal ∧ ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → π ∉ v'.asIdeal := by
  classical
  have hv0 : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have h1 : ClassGroup.mk0 (⟨v.asIdeal, hv0⟩ ^ h) = 1 := by
    rw [map_pow, hh, pow_card_eq_one]
  have h2 : (v.asIdeal ^ h).IsPrincipal := by
    have h3 : v.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv0 h
    rw [← ClassGroup.mk0_eq_one_iff h3, ← h1]
    rfl
  obtain ⟨π, hπ⟩ := h2
  have hπ' : v.asIdeal ^ h = Ideal.span {π} := hπ
  have hmem : π ∈ v.asIdeal ^ h := by rw [hπ']; exact Ideal.mem_span_singleton_self π
  refine ⟨π, Ideal.pow_le_self hpos.ne' hmem, fun v' hv' hc => hv' ?_⟩
  have hle : v.asIdeal ^ h ≤ v'.asIdeal := by
    rw [hπ', Ideal.span_singleton_le_iff_mem]; exact hc
  have hle' : v.asIdeal ≤ v'.asIdeal := v'.isPrime.le_of_pow_le hle
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle').symm

theorem b_mul_mem_map (P : Ideal (𝓞 E)) (c : 𝓞 E) (hc : c ∈ P) (t : RInt F E) :
    toRInt F E c * t ∈ P.map (toRInt F E) := by
  have h1 : toRInt F E c ∈ P.map (toRInt F E) := Ideal.mem_map_of_mem _ hc
  first
  | exact Ideal.mul_mem_right _ _ h1
  | exact Ideal.mul_mem_right t _ h1
  | exact Ideal.mul_mem_right t h1
  | exact (P.map (toRInt F E)).mul_mem_right t h1

theorem b_eps_mem (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) ≠ v.asIdeal) : bEps E v ∈ P.asIdeal.map (toRInt F E) := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  have hmax : (P.asIdeal.under (𝓞 F)).IsMaximal := Ideal.IsMaximal.under (𝓞 F) P.asIdeal
  have hnle : ¬ P.asIdeal.under (𝓞 F) ≤ v.asIdeal := fun hle =>
    hP (hmax.eq_of_le v.isPrime.ne_top hle)
  obtain ⟨π, hπ, hπv⟩ := SetLike.not_le_iff_exists.mp hnle
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v π hπv
  rw [← hρ]
  exact b_mul_mem_map P.asIdeal (algebraMap (𝓞 F) (𝓞 E) π) hπ ρ

theorem b_one_sub_eps_mem (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : 1 - bEps E v ∈ P.asIdeal.map (toRInt F E) := by
  obtain ⟨π, hπ, hπv⟩ := b_pi v
  obtain ⟨ρ, hρ⟩ := b_off_inv (E := E) v π hπv
  rw [← hρ]
  rw [← hP] at hπ
  exact b_mul_mem_map P.asIdeal (algebraMap (𝓞 F) (𝓞 E) π) hπ ρ

theorem tpOff_proof' (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) ≠ v.asIdeal) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E) := by
  rw [← b_eps_mul_unit v u hu]
  exact Ideal.mul_mem_right _ _ (b_eps_mem v P hP)

end B

section B2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem b_approx (D : 𝓞 F) (hD : D ≠ 0) (s : RInt F E) :
    ∃ (b : 𝓞 E) (t : RInt F E), s = toRInt F E b + toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t := by
  obtain ⟨b, t, ht, h⟩ := csGlob_approx csGlob_intAdApprox D hD (s : AfE F E) s.2
  refine ⟨b, ⟨t, ht⟩, Subtype.ext ?_⟩
  rw [h]
  show _ = ((toRInt F E b : RInt F E) : AfE F E) +
    ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) : RInt F E) : AfE F E) * t
  rw [b_toRInt_alg, b_toRInt_val]
  rfl

theorem b_under_elt (P : HeightOneSpectrum (𝓞 E)) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ algebraMap (𝓞 F) (𝓞 E) D ∈ P.asIdeal := by
  have hne : P.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P.ne_bot
  obtain ⟨D, hD, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨D, hD0, hD⟩

theorem tpApprox_proof' (P : HeightOneSpectrum (𝓞 E)) (s : RInt F E) :
    ∃ b : 𝓞 E, s - toRInt F E b ∈ P.asIdeal.map (toRInt F E) := by
  obtain ⟨D, hD0, hD⟩ := b_under_elt (F := F) P
  obtain ⟨b, t, h⟩ := b_approx D hD0 s
  refine ⟨b, ?_⟩
  rw [h, add_sub_cancel_left]
  exact b_mul_mem_map _ _ hD t

theorem b_map_shape (I : Ideal (𝓞 E)) (D : 𝓞 F) (hD0 : D ≠ 0)
    (s : RInt F E) (hs : s ∈ I.map (toRInt F E)) :
    ∃ c ∈ I, ∃ t : RInt F E, s = toRInt F E c + toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t := by
  unfold Ideal.map at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨c, hc, 0, by rw [mul_zero, add_zero]⟩
  | zero => exact ⟨0, I.zero_mem, 0, by rw [mul_zero, add_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, t, rfl⟩ := hx
    obtain ⟨c', hc', t', rfl⟩ := hy
    exact ⟨c + c', I.add_mem hc hc', t + t', by rw [map_add]; ring⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, t, rfl⟩ := hx
    obtain ⟨b, t', rfl⟩ := b_approx D hD0 a
    refine ⟨b * c, I.mul_mem_left b hc, toRInt F E b * t + t' * toRInt F E c +
      toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t' * t, ?_⟩
    rw [smul_eq_mul, map_mul]; ring

theorem b_comap (I : Ideal (𝓞 E)) (D : 𝓞 F) (hD0 : D ≠ 0) (hD : algebraMap (𝓞 F) (𝓞 E) D ∈ I)
    (c : 𝓞 E) (hc : toRInt F E c ∈ I.map (toRInt F E)) : c ∈ I := by
  obtain ⟨c', hc', t, h⟩ := b_map_shape I D hD0 _ hc
  have hDE : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E]
    exact adelstab_algebraMap_ne_zero D hD0
  set d : E := algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D) with hd
  have h1 : ((t : RInt F E) : AfE F E) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
    have h2 := congrArg (fun z : RInt F E => (z : AfE F E)) h
    simp only [Subring.coe_add, Subring.coe_mul, b_toRInt_val] at h2
    have h3 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d * (t : AfE F E) =
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d *
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
      rw [← map_mul, mul_div_cancel₀ _ hDE, map_sub, h2]
      ring
    have hu : IsUnit (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d) := (IsUnit.mk0 d hDE).map _
    exact hu.mul_left_cancel h3
  have hint : IsIntegral ℤ ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
    apply csGlob_int (F := F)
    rw [← h1]
    exact t.2
  let m : 𝓞 E := ⟨_, hint⟩
  have hm : c - c' = algebraMap (𝓞 F) (𝓞 E) D * m := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 E) E (c - c') = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D * m)
    rw [map_sub, map_mul]
    show _ = d * ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d)
    rw [mul_div_cancel₀ _ hDE]
  have : c = c' + algebraMap (𝓞 F) (𝓞 E) D * m := by rw [← hm]; ring
  rw [this]
  exact I.add_mem hc' (I.mul_mem_right _ hD)


theorem b_pow_mem (z : RInt F E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), z ∈ P.asIdeal.map (toRInt F E))
    (I : Ideal (𝓞 E)) : I ≠ 0 → ∃ k : ℕ, z ^ k ∈ I.map (toRInt F E) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff] at hx
    exact ⟨0, by rw [hx, Ideal.map_top]; trivial⟩
  | h₃ a p ha hp ih =>
    intro _
    obtain ⟨k, hk⟩ := ih ha
    refine ⟨k + 1, ?_⟩
    rw [Ideal.map_mul, pow_succ']
    exact Ideal.mul_mem_mul (hz ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩) hk

theorem b_plc_ne_zero (v : HeightOneSpectrum (𝓞 F)) : plc v ≠ 0 := by
  have := ringChar.charP (𝓞 F ⧸ v.asIdeal)
  exact CharP.char_ne_zero_of_finite (𝓞 F ⧸ v.asIdeal) (plc v)

theorem tpWild_proof' (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v := by
  refine ⟨⟨u, ?_, rfl⟩, hu⟩
  rw [SetLike.mem_coe, mem_kerRed]
  have hne : Ideal.span {((plc v : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact b_plc_ne_zero v
  obtain ⟨k, hk⟩ := b_pow_mem _ h _ hne
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at hk
  exact ⟨k, hk⟩

end B2

section B3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem b_intU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) :
    ∃ u : (RInt F E)ˣ, Units.map (RInt F E).subtype.toMonoidHom u = x := by
  rw [intU, Submonoid.mem_units_iff] at hx
  refine ⟨⟨⟨x, hx.1⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx.2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, Units.ext rfl⟩

theorem b_mkU (v : HeightOneSpectrum (𝓞 F)) (b c : 𝓞 E) (r : 𝓞 F) (hr : r ∉ v.asIdeal)
    (hbc : b * c = algebraMap (𝓞 F) (𝓞 E) r) :
    ∃ u : (RInt F E)ˣ, (u : RInt F E) = toRInt F E b * bEps E v + (1 - bEps E v) := by
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v r hr
  have hi := b_eps_idem (E := E) v
  rw [← hbc, map_mul] at hρ
  refine ⟨⟨toRInt F E b * bEps E v + (1 - bEps E v), toRInt F E c * ρ * bEps E v + (1 - bEps E v), ?_, ?_⟩, rfl⟩
  · have : (toRInt F E b * bEps E v + (1 - bEps E v)) * (toRInt F E c * ρ * bEps E v + (1 - bEps E v)) =
        (toRInt F E b * toRInt F E c * ρ) * (bEps E v * bEps E v) + 1 - 2 * bEps E v + bEps E v * bEps E v +
          (toRInt F E b + toRInt F E c * ρ) * (bEps E v - bEps E v * bEps E v) := by ring
    rw [this, hρ, hi, hi]; ring
  · have : (toRInt F E c * ρ * bEps E v + (1 - bEps E v)) * (toRInt F E b * bEps E v + (1 - bEps E v)) =
        (toRInt F E b * toRInt F E c * ρ) * (bEps E v * bEps E v) + 1 - 2 * bEps E v + bEps E v * bEps E v +
          (toRInt F E b + toRInt F E c * ρ) * (bEps E v - bEps E v * bEps E v) := by ring
    rw [this, hρ, hi, hi]; ring

theorem b_mkU_supp (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E) (u : (RInt F E)ˣ)
    (hu : (u : RInt F E) = toRInt F E b * bEps E v + (1 - bEps E v)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v := by
  rw [b_mem_suppAt]
  intro v' hv'
  show prV (E := E) v' ((u : RInt F E) : AfE F E) = 1
  rw [hu]
  show prV (E := E) v' (((toRInt F E b : RInt F E) : AfE F E) * afsplitEps E v + (1 - afsplitEps E v)) = 1
  rw [map_add, map_mul, map_sub, afsplit_prV_eps_ne v v' hv', mul_zero, map_one, sub_zero, zero_add]

theorem b_exists_mul (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E)
    (hb : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → b ∉ P.asIdeal) :
    ∃ (c : 𝓞 E) (r : 𝓞 F), r ∉ v.asIdeal ∧ b * c = algebraMap (𝓞 F) (𝓞 E) r := by
  by_contra hcon
  push Not at hcon
  have hle : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {b}) ≤ v.asIdeal := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hr
    obtain ⟨c, hc⟩ := hr
    by_contra hrv
    exact hcon c r hrv hc.symm
  have := v.isPrime
  obtain ⟨Q, hQ, hQp, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (Ideal.span {b}) hle
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  exact hb ⟨Q, hQp, hQ0⟩ hQv (hQ (Ideal.mem_span_singleton_self b))

theorem tpExU_proof' (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) (a : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ (u : (RInt F E)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a ∧
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v ∧
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  classical
  obtain ⟨b0, hb0⟩ := Ideal.Quotient.mk_surjective (a : 𝓞 E ⧸ P.asIdeal)
  have hb0P : b0 ∉ P.asIdeal := by
    intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem, hb0] at h
    have : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
    exact a.ne_zero h
  have hmap0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact v.ne_bot
  have hfin := Ideal.finite_factors hmap0
  have hmemT : ∀ P' : HeightOneSpectrum (𝓞 E), P'.asIdeal.under (𝓞 F) = v.asIdeal → P' ∈ hfin.toFinset := by
    intro P' hP'
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hP']
  obtain ⟨b', hb'⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun Q => if (Q : HeightOneSpectrum (𝓞 E)) = P then b0 else 1)
  have hbP : b' - b0 ∈ P.asIdeal := by
    have := hb' P (hmemT P hPv)
    rwa [if_pos rfl, pow_one] at this
  have hbP' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal →
      b' - 1 ∈ P'.asIdeal := by
    intro P' hne hP'
    have := hb' P' (hmemT P' hP')
    rwa [if_neg hne, pow_one] at this
  have hnot : ∀ Q : HeightOneSpectrum (𝓞 E), Q.asIdeal.under (𝓞 F) = v.asIdeal → b' ∉ Q.asIdeal := by
    intro Q hQ hmem
    by_cases h : Q = P
    · subst h
      apply hb0P
      have := Q.asIdeal.sub_mem hmem hbP
      rwa [sub_sub_cancel] at this
    · apply Q.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have := Q.asIdeal.sub_mem hmem (hbP' Q h hQ)
      rwa [sub_sub_cancel] at this
  obtain ⟨c, r, hr, hbc⟩ := b_exists_mul v b' hnot
  obtain ⟨u, hu⟩ := b_mkU v b' c r hr hbc
  refine ⟨u, b0, hb0, b_mkU_supp v b' u hu, ?_, ?_⟩
  · have : (u : RInt F E) - toRInt F E b0 =
        toRInt F E (b' - b0) * bEps E v + (1 - toRInt F E b0) * (1 - bEps E v) := by
      rw [hu, map_sub]; ring
    rw [this]
    exact Ideal.add_mem _ (b_mul_mem_map _ _ hbP _) (Ideal.mul_mem_left _ _ (b_one_sub_eps_mem v P hPv))
  · intro P' hne
    have : (u : RInt F E) - 1 = toRInt F E (b' - 1) * bEps E v := by
      rw [hu, map_sub, map_one]; ring
    rw [this]
    by_cases hP' : P'.asIdeal.under (𝓞 F) = v.asIdeal
    · exact b_mul_mem_map _ _ (hbP' P' hne hP') _
    · exact Ideal.mul_mem_left _ _ (b_eps_mem v P' hP')

def bUnder (F : Type) [Field F] [NumberField F] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 F) :=
  ⟨P.asIdeal.under (𝓞 F), have := P.isPrime; inferInstance, Ideal.under_ne_bot (𝓞 F) P.ne_bot⟩

variable {L : Type} [Field L]

theorem b_same (ξ : Chr F E L) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (u u' : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (hu' : Units.map (RInt F E).subtype.toMonoidHom u' ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - u' ∈ P.asIdeal.map (toRInt F E)) :
    ξ (Units.map (RInt F E).subtype.toMonoidHom u) = ξ (Units.map (RInt F E).subtype.toMonoidHom u') := by
  have hw : Units.map (RInt F E).subtype.toMonoidHom (u * u'⁻¹) ∈ wildAt E v := by
    apply tpWild_proof'
    · rw [map_mul, map_inv]
      exact mul_mem hu (inv_mem hu')
    · intro P
      have : ((u * u'⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 = ((u : RInt F E) - u') * ((u'⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.mul_inv, Units.val_mul]
      rw [this]
      exact Ideal.mul_mem_right _ _ (h P)
  have h1 := hξ v hw
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem residue_character_exists : ResCharEx := by
  intro F E _ _ _ _ _ L _ ξ hξ P
  classical
  set v := bUnder F P with hv
  have hPv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  choose U B hB hU hUP hUP' using tpExU_proof' P v hPv
  have key : ∀ (u : (RInt F E)ˣ) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a →
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)) →
      ξ (Units.map (RInt F E).subtype.toMonoidHom u) = ξ (Units.map (RInt F E).subtype.toMonoidHom (U a)) := by
    intro u a b hb hu huP huP'
    apply b_same ξ hξ v u (U a) hu (hU a)
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      have hbb : b - B a ∈ Q.asIdeal := by
        rw [← Ideal.Quotient.eq, hb, hB]
      have : (u : RInt F E) - U a = ((u : RInt F E) - toRInt F E b) - ((U a : RInt F E) - toRInt F E (B a)) +
          toRInt F E (b - B a) := by rw [map_sub]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.sub_mem _ huP (hUP a)) (Ideal.mem_map_of_mem _ hbb)
    · have : (u : RInt F E) - U a = ((u : RInt F E) - 1) - ((U a : RInt F E) - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (huP' Q hQ) (hUP' a Q hQ)
  let χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ := MonoidHom.mk' (fun a => ξ (Units.map (RInt F E).subtype.toMonoidHom (U a))) (by
    intro a a'
    rw [← map_mul, ← map_mul]
    symm
    apply key (U a * U a') (a * a') (B a * B a')
    · rw [map_mul, hB, hB, Units.val_mul]
    · rw [map_mul]; exact mul_mem (hU a) (hU a')
    · have : ((U a * U a' : (RInt F E)ˣ) : RInt F E) - toRInt F E (B a * B a') =
          ((U a : RInt F E) - toRInt F E (B a)) * (U a' : RInt F E) +
            toRInt F E (B a) * ((U a' : RInt F E) - toRInt F E (B a')) := by
        rw [map_mul, Units.val_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hUP a)) (Ideal.mul_mem_left _ _ (hUP a'))
    · intro P' hP'
      have : ((U a * U a' : (RInt F E)ˣ) : RInt F E) - 1 =
          ((U a : RInt F E) - 1) * (U a' : RInt F E) + ((U a' : RInt F E) - 1) := by
        rw [Units.val_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hUP' a P' hP')) (hUP' a' P' hP'))
  refine ⟨χ, ?_, ?_⟩
  · intro v' hv' u a b hb hu huP huP'
    have : v' = v := HeightOneSpectrum.ext (hv'.symm.trans hPv)
    subst this
    exact key u a b hb hu huP huP'
  · intro χ' hχ'
    ext a
    rw [← hχ' v hPv (U a) a (B a) (hB a) (hU a) (hUP a) (hUP' a)]
    rfl

theorem b_resChar_spec (ξ : Chr F E L) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : IsResChar ξ P (resChar ξ P) := by
  have h : ∃ χ, IsResChar ξ P χ := (residue_character_exists F E L ξ hξ P).exists
  rw [resChar, dif_pos h]
  exact h.choose_spec


end B3

section B4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem auxiliary_primes_finite : QprimeFinite := by
  intro F E _ _ _ _ _ L _ ξ hξ
  obtain ⟨N, hN, hker⟩ := hξ
  have hN0 : Ideal.span {((N : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hN.ne'
  apply (Ideal.finite_factors hN0).subset
  intro v hv
  rw [Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hNv
  apply hv
  refine le_trans ?_ hker
  rintro x ⟨hx1, hx2⟩
  obtain ⟨u, rfl⟩ := b_intU x hx1
  refine ⟨u, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_kerRed, ← b_eps_mul_unit v u hx2]
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v _ hNv
  rw [← hρ, map_natCast, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem under_eq_of_le_lemma {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)}
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal) : P.asIdeal.under (𝓞 F) = v.asIdeal := by
  have h1 : v.asIdeal ≤ P.asIdeal.under (𝓞 F) := Ideal.map_le_iff_le_comap.mp h
  exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h1).symm

theorem b_under_of_split (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    P.asIdeal.under (𝓞 F) = v.asIdeal ∧ P'.asIdeal.under (𝓞 F) = v.asIdeal := by
  have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by
    rw [h]
    first
    | exact Ideal.mul_le_right
    | exact le_trans Ideal.mul_le_inf inf_le_left
    | exact Ideal.mul_le.mpr (fun r hr s _ => Ideal.mul_mem_right _ _ hr)
  have h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P'.asIdeal := by
    rw [h]
    first
    | exact Ideal.mul_le_left
    | exact le_trans Ideal.mul_le_inf inf_le_right
    | exact Ideal.mul_le.mpr (fun r _ s hs => Ideal.mul_mem_left _ _ hs)
  exact ⟨under_eq_of_le_lemma h1, under_eq_of_le_lemma h2⟩

private theorem hs_eq_lemma_2 {P Q : HeightOneSpectrum (𝓞 E)} (h : P.asIdeal = Q.asIdeal) : P = Q := by
  first
  | exact HeightOneSpectrum.ext h
  | (cases P; cases Q; cases h; rfl)

theorem b_other_of_split (v : HeightOneSpectrum (𝓞 F)) (P P' Q : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (hQ : Q ≠ P) (hQ' : Q ≠ P') :
    Q.asIdeal.under (𝓞 F) ≠ v.asIdeal := by
  intro hQv
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hQv.symm)
  rw [h] at hle
  rcases (Ideal.IsPrime.mul_le Q.isPrime).mp hle with h1 | h1
  · exact hQ (hs_eq_lemma_2 (P.isMaximal.eq_of_le Q.isPrime.ne_top h1).symm)
  · exact hQ' (hs_eq_lemma_2 (P'.isMaximal.eq_of_le Q.isPrime.ne_top h1).symm)




end B4

def TpExU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ∀ a : (𝓞 E ⧸ P.asIdeal)ˣ, ∃ (u : (RInt F E)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a ∧
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v ∧
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)

def TpWild : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ),
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
    (∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)) →
    Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v

def TpApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (s : RInt F E), ∃ b : 𝓞 E, s - toRInt F E b ∈ P.asIdeal.map (toRInt F E)

def TpComap : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), toRInt F E c ∈ P.asIdeal.map (toRInt F E) → c ∈ P.asIdeal

def TpOff : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) ≠ v.asIdeal →
    ∀ u : (RInt F E)ˣ, Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)

section D1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem d_under {v : HeightOneSpectrum (𝓞 F)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    P.asIdeal.under (𝓞 F) = v.asIdeal := by
  exact (b_under_of_split v P P' hv).1

theorem d_absNorm_map (hdeg : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal) = Ideal.absNorm v.asIdeal ^ 2 := by
  rw [← Ideal.absNorm_relNorm (R := 𝓞 F), Ideal.relNorm_algebraMap, map_pow,
    ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, hdeg]

def d_resMap (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : (𝓞 F ⧸ v.asIdeal) →+* (𝓞 E ⧸ P.asIdeal) :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) (le_of_eq h.symm)

theorem d_resMap_inj (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : Function.Injective (d_resMap v P h) := by
  first
  | exact Ideal.quotientMap_injective' (le_of_eq h)
  | (unfold d_resMap
     exact Ideal.quotientMap_injective' (le_of_eq h))
  | (haveI := v.isMaximal
     letI := Ideal.Quotient.field v.asIdeal
     haveI : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial P.isPrime.ne_top
     exact RingHom.injective _)

theorem d_finite_quot (P : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot

theorem d_absNorm_le (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : Ideal.absNorm v.asIdeal ≤ Ideal.absNorm P.asIdeal := by
  haveI := d_finite_quot P
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_le_card_of_injective _ (d_resMap_inj v P h)

theorem d_absNorm_eq (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  have hP := d_absNorm_le v P (d_under hv)
  have hP' := d_absNorm_le v P' (d_under (P := P') (P' := P) (by rw [hv, mul_comm]))
  have hmul := d_absNorm_map hdeg v
  rw [hv, map_mul] at hmul
  have hpos : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm v.asIdeal ≤
      Ideal.absNorm v.asIdeal * Ideal.absNorm v.asIdeal := by
    calc _ ≤ Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal := Nat.mul_le_mul le_rfl hP'
      _ = _ := by rw [hmul, sq]
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) hP

theorem d_resMap_surj (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    Function.Surjective (d_resMap v P (d_under hv)) := by
  have hi := d_resMap_inj v P (d_under hv)
  haveI := d_finite_quot P
  have hc : Nat.card (𝓞 E ⧸ P.asIdeal) ≤ Nat.card (𝓞 F ⧸ v.asIdeal) := by
    have := d_absNorm_eq hdeg hv
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at this
    exact this.le
  exact (hi.bijective_of_nat_card_le hc).2

theorem d_res_one (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (b : 𝓞 E) :
    ∃ n : 𝓞 F, b - algebraMap (𝓞 F) (𝓞 E) n ∈ P.asIdeal := by
  obtain ⟨x, hx⟩ := d_resMap_surj hdeg hv (Ideal.Quotient.mk P.asIdeal b)
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq]
  first
  | exact hx.symm
  | simpa [d_resMap] using hx.symm


end D1

section D2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom

theorem d_isRes (hEx : ResCharEx) (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : IsResChar ξ P (resChar ξ P) := by
  have h : ∃ χ, IsResChar ξ P χ := (hEx F E L ξ ht P).exists
  rw [resChar, dif_pos h]
  exact h.choose_spec

theorem d_isUnit_mk (P : HeightOneSpectrum (𝓞 E)) {b : 𝓞 E} (hb : b ∉ P.asIdeal) :
    IsUnit (Ideal.Quotient.mk P.asIdeal b) := by
  first
  | (obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hb
     refine isUnit_of_mul_eq_one _ (Ideal.Quotient.mk P.asIdeal y) ?_
     rw [← map_mul, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
     have e : b * y - 1 = -i := by rw [← hyi]; ring
     rw [e]
     exact P.asIdeal.neg_mem hi)
  | (haveI := P.isMaximal
     letI := Ideal.Quotient.field P.asIdeal
     exact isUnit_iff_ne_zero.mpr (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)))

theorem d_lift_intU {x : (AfE F E)ˣ} (hx : x ∈ intU F E) : ∃ u : (RInt F E)ˣ, uIn u = x := by
  exact b_intU x hx

theorem d_mem_intU (u : (RInt F E)ˣ) : uIn u ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff]
  exact ⟨u.1.2, (u⁻¹).1.2⟩

theorem d_not_mem (hC : TpComap) (P : HeightOneSpectrum (𝓞 E)) (u : (RInt F E)ˣ) (b : 𝓞 E)
    (h : (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E)) : b ∉ P.asIdeal := by
  intro hb
  have h1 : toRInt F E b ∈ P.asIdeal.map (toRInt F E) := Ideal.mem_map_of_mem _ hb
  have h2 : (u : RInt F E) ∈ P.asIdeal.map (toRInt F E) := by
    have := add_mem h h1
    rwa [sub_add_cancel] at this
  have h3 : (1 : RInt F E) ∈ P.asIdeal.map (toRInt F E) := by
    have := Ideal.mul_mem_left _ ((u⁻¹ : (RInt F E)ˣ) : RInt F E) h2
    rwa [Units.inv_mul] at this
  have h4 : (1 : 𝓞 E) ∈ P.asIdeal := hC F E P 1 (by rw [map_one]; exact h3)
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h4)

theorem d_other {v : HeightOneSpectrum (𝓞 F)} {P P' Q : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (h1 : Q ≠ P) (h2 : Q ≠ P') :
    Q.asIdeal.under (𝓞 F) ≠ v.asIdeal := by
  exact b_other_of_split v P P' Q hv h1 h2

theorem d_formula (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) (hdeg : Module.finrank F E = 2)
    (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (hF : (idF F E).range ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P')
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal)
    (x : (AfE F E)ˣ) (hx : x ∈ inertAt E v) :
    ∃ a a'' : (𝓞 E ⧸ P.asIdeal)ˣ, ξ x = resChar ξ P a * (resChar ξ P a'')⁻¹ := by
  have hv' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P'.asIdeal * P.asIdeal := by rw [hv, mul_comm]
  have hPv := d_under hv
  have hPv' := d_under hv'
  obtain ⟨u, rfl⟩ := d_lift_intU hx.1
  have hsu := hx.2
  obtain ⟨b, hb⟩ := hA F E P (u : RInt F E)
  obtain ⟨b', hb'⟩ := hA F E P' (u : RInt F E)
  obtain ⟨n, hn⟩ := d_res_one hdeg hv' b'
  have hun : (u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) ∈ P'.asIdeal.map (toRInt F E) := by
    have h1 : toRInt F E (b' - algebraMap (𝓞 F) (𝓞 E) n) ∈ P'.asIdeal.map (toRInt F E) :=
      Ideal.mem_map_of_mem _ hn
    have h2 := add_mem hb' h1
    rw [map_sub] at h2
    convert h2 using 1
    ring
  have hbP := d_not_mem hC P u b hb
  have hnP' := d_not_mem hC P' u _ hun
  have hnv : n ∉ v.asIdeal := by
    intro h
    apply hnP'
    rw [← hPv'] at h
    exact h
  have hnP : algebraMap (𝓞 F) (𝓞 E) n ∉ P.asIdeal := by
    intro h
    apply hnv
    rw [← hPv]
    exact h
  obtain ⟨a, ha⟩ := d_isUnit_mk P hbP
  obtain ⟨a', ha'⟩ := d_isUnit_mk P' hnP'
  obtain ⟨a'', ha''⟩ := d_isUnit_mk P hnP
  have hc := hConj F E L ξ ht hF v P P' hne hv n a'' a' ha'' ha'
  obtain ⟨u1, b1, hb1, hs1, hc1, ho1⟩ := hExU F E P v hPv a
  obtain ⟨u2, b2, hb2, hs2, hc2, ho2⟩ := hExU F E P' v hPv' a'
  have e1 : ξ (uIn u1) = resChar ξ P a := d_isRes hEx ξ ht P v hPv u1 a b1 hb1 hs1 hc1 ho1
  have e2 : ξ (uIn u2) = resChar ξ P' a' := d_isRes hEx ξ ht P' v hPv' u2 a' b2 hb2 hs2 hc2 ho2
  have hdiff : ∀ Q : HeightOneSpectrum (𝓞 E), (u : RInt F E) - u1 * u2 ∈ Q.asIdeal.map (toRInt F E) := by
    intro Q
    by_cases h1 : Q = P
    · subst h1
      have t2 := Ideal.mul_mem_right (u2 : RInt F E) _ hc1
      have t3 := Ideal.mul_mem_left _ (toRInt F E b1) (ho2 Q hne)
      have t4 : toRInt F E (b1 - b) ∈ Q.asIdeal.map (toRInt F E) :=
        Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp (hb1.trans ha))
      have t := sub_mem (sub_mem (sub_mem hb t2) t3) t4
      rw [map_sub] at t
      convert t using 1
      ring
    · by_cases h2 : Q = P'
      · subst h2
        have t2 := Ideal.mul_mem_right (u1 : RInt F E) _ hc2
        have t3 := Ideal.mul_mem_left _ (toRInt F E b2) (ho1 Q hne.symm)
        have t4 : toRInt F E (b2 - algebraMap (𝓞 F) (𝓞 E) n) ∈ Q.asIdeal.map (toRInt F E) :=
          Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp (hb2.trans ha'))
        have t := sub_mem (sub_mem (sub_mem hun t2) t3) t4
        rw [map_sub] at t
        convert t using 1
        ring
      · have hQ := d_other hv h1 h2
        have t1 := hO F E v Q hQ u hsu
        have t2 := Ideal.mul_mem_right (u2 : RInt F E) _ (hO F E v Q hQ u1 hs1)
        have t3 := hO F E v Q hQ u2 hs2
        have t := sub_mem (sub_mem t1 t2) t3
        convert t using 1
        ring
  have hw : uIn (u * (u1 * u2)⁻¹) ∈ wildAt E v := by
    apply hW F E v
    · rw [map_mul, map_inv, map_mul]
      exact mul_mem hsu (inv_mem (mul_mem hs1 hs2))
    · intro Q
      have h1 : ((u * (u1 * u2)⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 =
          ((u : RInt F E) - u1 * u2) * (((u1 * u2)⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.val_mul, ← Units.val_mul u1 u2, Units.mul_inv]
      rw [h1]
      exact Ideal.mul_mem_right _ _ (hdiff Q)
  have hk : ξ (uIn (u * (u1 * u2)⁻¹)) = 1 := MonoidHom.mem_ker.mp (ht v hw)
  simp only [map_mul, map_inv] at hk
  rw [e1, e2] at hk
  refine ⟨a, a'', ?_⟩
  rw [mul_inv_eq_one.mp hk, eq_inv_of_mul_eq_one_right hc]

theorem d_key (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) (hdeg : Module.finrank F E = 2)
    (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (hF : (idF F E).range ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P')
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (m : ℕ) :
    (∀ x ∈ inertAt E v, ξ x ^ m = 1) ↔ resChar ξ P ^ m = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro a
    obtain ⟨u1, b1, hb1, hs1, hc1, ho1⟩ := hExU F E P v (d_under hv) a
    have e1 := d_isRes hEx ξ ht P v (d_under hv) u1 a b1 hb1 hs1 hc1 ho1
    rw [MonoidHom.pow_apply, ← e1, MonoidHom.one_apply]
    exact h _ ⟨d_mem_intU u1, hs1⟩
  · intro h x hx
    obtain ⟨a, a'', e⟩ := d_formula hExU hW hA hC hO hEx hConj hdeg ξ ht hF v P P' hne hv x hx
    have h1 : ∀ c, resChar ξ P c ^ m = 1 := fun c => by
      rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
    rw [e, mul_pow, inv_pow, h1, h1, inv_one, mul_one]

end D2













end Formalism.L2.DIV

end
