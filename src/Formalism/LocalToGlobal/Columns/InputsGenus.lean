module

public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists
public import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
public import Formalism.LocalToGlobal.Columns.Inputs
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Mathlib.RingTheory.PiTensorProduct
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.ComplF

section
@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

def GenusToPoint : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N →
    Formalism.HermitianLatticesTheory.SameGenus (hStd E n) (stdLat E n) N → ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

def LocToAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), UnimodGenusLoc E n → UnimodGenus hc n

end Formalism.L2.GenusGluing.Gen
end
end
end


section
@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_sum_apply {ι : Type} (T : Finset ι) (f : ι → Formalism.L2.Herm.Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ T, f v) w = ∑ v ∈ T, f v w := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

theorem one_tmul_mem (a : Formalism.L2.Herm.Af F) (h : a ∈ Formalism.UG.intAd F) :
    (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E :=
  (Formalism.L2.DIV.adS F E ⟨a, h⟩).2

theorem iA_algebraMap (r : 𝓞 F) :
    iA F E (algebraMap (𝓞 F) E r) = (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) r := by
  have := Formalism.UG.P.csGlob_tmul_int (F := F) (E := E) (1 : E) r
  rw [mul_one] at this
  exact this.symm

theorem iA_algebraMap_mem (r : 𝓞 F) : iA F E (algebraMap (𝓞 F) E r) ∈ Formalism.L2.Herm.intAf F E := by
  rw [iA_algebraMap]
  exact one_tmul_mem _ (Formalism.UG.P.levelaf_int_mem r)

theorem eP_mem (P : HeightOneSpectrum (𝓞 F) → Prop) : eP E P ∈ Formalism.L2.Herm.intAf F E :=
  (Formalism.L2.DIV.adS F E (Formalism.L2.DIV.idemAd P)).2

theorem eP_mul_mem (P : HeightOneSpectrum (𝓞 F) → Prop) (c : 𝓞 F) (hc : ∀ w, P w → c ∉ w.asIdeal)
    (u : E ⊗[F] Formalism.L2.Herm.Af F) (hu : iA F E (algebraMap (𝓞 F) E c) * u ∈ Formalism.L2.Herm.intAf F E) :
    eP E P * u ∈ Formalism.L2.Herm.intAf F E := by
  classical
  have hw : ∀ w : HeightOneSpectrum (𝓞 F),
      (if P w then (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹ else 0) ∈ w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact Formalism.L2.DIV.fr_inv_int w c (hc w h)
    · exact zero_mem _
  set wA : Formalism.UG.intAd F := Formalism.L2.DIV.mkAd _ hw with hwA
  have hprod : algebraMap (𝓞 F) (Formalism.L2.Herm.Af F) c * (wA : Formalism.L2.Herm.Af F) =
      ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) := by
    ext1 w
    show algebraMap (𝓞 F) (w.adicCompletion F) c * ((wA : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w =
      ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w
    rw [hwA, Formalism.L2.DIV.mkAd_apply]
    by_cases h : P w
    · rw [ite_eq_left h, Formalism.L2.DIV.idemAd_pos h]
      refine mul_inv_cancel₀ (Formalism.UG.P.levelaf_algebraMap_ne_zero w c ?_)
      rintro rfl
      exact hc w h (Ideal.zero_mem _)
    · rw [ite_eq_right h, Formalism.L2.DIV.idemAd_neg h, mul_zero]
  have key : eP E P = (1 : E) ⊗ₜ[F] (wA : Formalism.L2.Herm.Af F) * iA F E (algebraMap (𝓞 F) E c) := by
    rw [iA_algebraMap, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, hprod]
    rfl
  rw [key, mul_assoc]
  exact mul_mem (one_tmul_mem _ wA.2) hu

end SlopeTestRemainingChoices

theorem idempotentCalculation_holds : IdemCalc := by
  intro F E _ _ _ _ _
  refine ⟨fun P => eP_mem P, fun P Q => ?_, fun T => ?_⟩
  · show (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) *
        (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd Q : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) =
      (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun v => P v ∧ Q v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ext1 w
    show ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w *
        ((Formalism.L2.DIV.idemAd Q : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w =
      ((Formalism.L2.DIV.idemAd (fun v => P v ∧ Q v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w
    by_cases hP : P w
    · by_cases hQ : Q w
      · rw [Formalism.L2.DIV.idemAd_pos hP, Formalism.L2.DIV.idemAd_pos hQ,
          Formalism.L2.DIV.idemAd_pos (P := fun v => P v ∧ Q v) ⟨hP, hQ⟩, one_mul]
      · rw [Formalism.L2.DIV.idemAd_neg hQ, Formalism.L2.DIV.idemAd_neg (P := fun v => P v ∧ Q v) (fun h => hQ h.2),
          mul_zero]
    · rw [Formalism.L2.DIV.idemAd_neg hP, Formalism.L2.DIV.idemAd_neg (P := fun v => P v ∧ Q v) (fun h => hP h.1),
        zero_mul]
  · show ∑ v ∈ T, (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) +
        (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun v => v ∉ T) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) = 1
    rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_add, Algebra.TensorProduct.one_def]
    congr 1
    ext1 w
    show (∑ v ∈ T, ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)) w +
        ((Formalism.L2.DIV.idemAd (fun v => v ∉ T) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) w = 1
    rw [adele_sum_apply]
    by_cases hw : w ∈ T
    · rw [Finset.sum_eq_single w, Formalism.L2.DIV.idemAd_pos (P := fun x => x = w) rfl,
        Formalism.L2.DIV.idemAd_neg (P := fun x => x ∉ T) (not_not.2 hw), add_zero]
      · intro b _ hb
        exact Formalism.L2.DIV.idemAd_neg (P := fun x => x = b) (v := w) (fun h => hb h.symm)
      · intro h
        exact absurd hw h
    · rw [Finset.sum_eq_zero, Formalism.L2.DIV.idemAd_pos (P := fun x => x ∉ T) hw, zero_add]
      intro b hb
      exact Formalism.L2.DIV.idemAd_neg (P := fun x => x = b) (v := w) (fun h => hw (by subst h; exact hb))

theorem idempotentIntegral_holds : IdemInt := by
  intro F E _ _ _ _ _ v r hr u hu
  exact eP_mul_mem _ r (fun w hw => by subst hw; exact hr) u hu

theorem idempotentCofinite_holds : IdemCof := by
  intro F E _ _ _ _ _ D _ u hu
  exact eP_mul_mem _ D (fun _ h => h) u hu

theorem idempotentDenominator_holds : IdemDenom := by
  intro F E _ _ _ _ _ v u hu
  obtain ⟨d, hd0, hd⟩ := Formalism.UG.P.levelaf_denom (F := F) (E := E) u
  rw [Formalism.UG.P.levelafC, ← iA_algebraMap] at hd
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hD : d * π ≠ 0 := mul_ne_zero hd0 hπ0
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F (d * π) hD
    ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) (Formalism.L2.DIV.idemAd _).2
  refine ⟨r, fun hr => ?_, ?_⟩
  · have h2 : ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) v =
        algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) (d * π) * y v :=
      congrArg (fun z : Formalism.L2.Herm.Af F => z v) e
    rw [Formalism.L2.DIV.idemAd_pos (P := fun w => w = v) (v := v) rfl] at h2
    have hrv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
      rw [Formalism.UG.P.csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
    have hDv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (d * π)) < 1 := by
      rw [Formalism.UG.P.csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 (Ideal.mul_mem_left _ d hπv)
    have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v)
    have h1 : Valued.v (1 : v.adicCompletion F) < 1 := by
      rw [h2]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hrv ?_)
      rw [map_mul]
      exact mul_lt_one_of_lt_of_le hDv hyv
    rw [map_one] at h1
    exact lt_irrefl _ h1
  · have hid : eAt E v = iA F E (algebraMap (𝓞 F) E r) +
        iA F E (algebraMap (𝓞 F) E π) * (1 : E) ⊗ₜ[F] y * iA F E (algebraMap (𝓞 F) E d) := by
      show (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) = _
      rw [e, iA_algebraMap, iA_algebraMap, iA_algebraMap, TensorProduct.tmul_add,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, map_mul]
      congr 2
      ring
    have hsub : iA F E (algebraMap (𝓞 F) E r) * u = eAt E v * u -
        iA F E (algebraMap (𝓞 F) E π) * (1 : E) ⊗ₜ[F] y * (iA F E (algebraMap (𝓞 F) E d) * u) := by
      rw [hid]; ring
    rw [hsub]
    exact sub_mem hu (mul_mem (mul_mem (iA_algebraMap_mem π) (one_tmul_mem y hy)) hd)

theorem memLocalizedStd_holds : MemLocFStd := by
  intro F E _ _ _ _ _ n v z
  have halg : ∀ r : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap (𝓞 F) E r :=
    fun r => (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E r).symm
  constructor
  · rintro ⟨s, hs, hsz⟩
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hs
    have hr' : r ∉ v.asIdeal := hr
    intro i
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hsz) i (Set.mem_univ i))
    refine idempotentIntegral_holds F E v r hr' _ ?_
    rw [← map_mul]
    have : algebraMap (𝓞 F) E r * z i = algebraMap (𝓞 E) E b := by
      rw [hb, ← halg]
      rfl
    rw [this]
    exact Formalism.UG.CS.incl_int b
  · intro h
    have h' : ∀ i, ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (𝓞 F) E r * z i) := by
      intro i
      obtain ⟨r, hr, hm⟩ := idempotentDenominator_holds F E v _ (h i)
      rw [← map_mul] at hm
      exact ⟨r, hr, Formalism.UG.P.csGlob_int _ hm⟩
    choose r hr hint using h'
    refine ⟨algebraMap (𝓞 F) (𝓞 E) (∏ i, r i),
      Submonoid.mem_map_of_mem _ (Submonoid.prod_mem _ (fun i _ => (hr i : r i ∈ v.asIdeal.primeCompl))), ?_⟩
    refine Submodule.mem_pi.2 (fun i _ => Submodule.mem_one.2 ?_)
    obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = algebraMap (𝓞 F) E (r i) * z i :=
      ⟨⟨_, hint i⟩, rfl⟩
    refine ⟨algebraMap (𝓞 F) (𝓞 E) (∏ j ∈ Finset.univ.erase i, r j) * b, ?_⟩
    show _ = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) (∏ i, r i)) * z i
    rw [map_mul, hb, halg, halg, ← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i), map_mul]
    ring

end Formalism.L2.GenusGluing.Gen
end
end
end


section
@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section Alg

variable {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]

def glueM (e : A) (M : Matrix m m A) : Matrix m m A := e • M + (1 - e) • (1 : Matrix m m A)

theorem glueM_mul {e : A} (he : e * e = e) (X Y : Matrix m m A) :
    glueM e X * glueM e Y = glueM e (X * Y) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [glueM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
    Matrix.one_mul, h1, h2, h3, he, zero_smul, add_zero, zero_add]

theorem glueM_one (e : A) : glueM e (1 : Matrix m m A) = 1 := by
  rw [glueM, ← add_smul, add_sub_cancel, one_smul]

def glueU {e : A} (he : e * e = e) (g : GL m A) : GL m A where
  val := glueM e (g : Matrix m m A)
  inv := glueM e ((g⁻¹ : GL m A) : Matrix m m A)
  val_inv := by rw [glueM_mul he, Units.mul_inv, glueM_one]
  inv_val := by rw [glueM_mul he, Units.inv_mul, glueM_one]

theorem glueU_val {e : A} (he : e * e = e) (g : GL m A) :
    ((glueU he g : GL m A) : Matrix m m A) = glueM e (g : Matrix m m A) := rfl

theorem cT_glueM (σ : A →+* A) {e : A} (hσ : σ e = e) (M : Matrix m m A) :
    Formalism.UG.cT σ (glueM e M) = glueM e (Formalism.UG.cT σ M) := by
  ext a b
  simp only [Formalism.UG.cT, glueM, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ]
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem glueU_mem (σ : A →+* A) {e : A} (he : e * e = e) (hσ : σ e = e) {g : GL m A}
    (hg : g ∈ Formalism.UG.UJ σ (1 : Matrix m m A)) : glueU he g ∈ Formalism.UG.UJ σ (1 : Matrix m m A) := by
  have hg' : Formalism.UG.cT σ (g : Matrix m m A) * 1 * (g : Matrix m m A) = 1 := hg
  show Formalism.UG.cT σ ((glueU he g : GL m A) : Matrix m m A) * 1 * ((glueU he g : GL m A) : Matrix m m A) = 1
  rw [glueU_val, cT_glueM σ hσ, Matrix.mul_one, glueM_mul he]
  rw [Matrix.mul_one] at hg'
  rw [hg', glueM_one]

theorem glue_smul_zero {f e : A} (hfe : f * e = 0) (M Y : Matrix m m A) :
    f • (glueM e M * Y) = f • Y := by
  rw [glueM, add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul, smul_smul,
    hfe, zero_smul, zero_add, mul_sub, mul_one, hfe, sub_zero]

theorem glue_smul_same {f e : A} (hfe : f * e = f) (M Y : Matrix m m A) :
    f • (glueM e M * Y) = f • (M * Y) := by
  rw [glueM, add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul, smul_smul,
    hfe, mul_sub, mul_one, hfe, sub_self, zero_smul, add_zero]

end Alg

section Idem

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem eP_congr {P Q : HeightOneSpectrum (𝓞 F) → Prop} (h : ∀ v, P v ↔ Q v) : eP E P = eP E Q := by
  have hPQ : P = Q := funext fun v => propext (h v)
  subst hPQ
  rfl

theorem eP_false : eP E (fun _ : HeightOneSpectrum (𝓞 F) => False) = 0 := by
  have h0 : ((Formalism.L2.DIV.idemAd (fun _ : HeightOneSpectrum (𝓞 F) => False) : Formalism.UG.intAd F)
      : Formalism.L2.Herm.Af F) = 0 := by
    ext v
    rw [Formalism.L2.DIV.idemAd_neg (P := fun _ : HeightOneSpectrum (𝓞 F) => False) (v := v) (fun h => h)]
    rfl
  rw [eP, h0, TensorProduct.tmul_zero]

theorem sigR_eP [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (P : HeightOneSpectrum (𝓞 F) → Prop) :
    Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eP E P) = eP E P := by
  rw [Formalism.UG.sigR, eP]
  simp

end Idem

theorem glueExists_of : IdemCalc → GlueExists := by
  intro hI F E _ _ _ _ _ _ hc n T γ
  classical
  have hmul : ∀ P Q : HeightOneSpectrum (𝓞 F) → Prop, eP E P * eP E Q = eP E (fun v => P v ∧ Q v) :=
    (hI F E).2.1
  have hAt : ∀ v : HeightOneSpectrum (𝓞 F), eAt E v = eP E (fun w => w = v) := fun v => rfl
  suffices key : ∃ y ∈ UAd hc n,
      (∀ v ∈ T, eAt E v • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        eAt E v • ((Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) ∧
      eP E (fun v => v ∉ T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        eP E (fun v => v ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) by
    obtain ⟨y, hy, h1, h2⟩ := key
    refine ⟨y⁻¹, inv_mem hy, ?_, ?_⟩
    · intro v hv; rw [inv_inv]; exact h1 v hv
    · rw [inv_inv]; exact h2
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), rfl⟩
  | insert v T hv ih =>
    obtain ⟨y, hy, h1, h2⟩ := ih
    have hgU : Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹) ∈ UAd hc n := (ratIn hc n (γ v)⁻¹).2
    have hev : eAt E v * eAt E v = eAt E v := by
      rw [hAt, hmul]; exact eP_congr (fun u => and_self_iff)
    have hσ : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
    have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have hgU' : Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹) ∈
        Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)) (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      have h := hgU
      change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
        ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) at h
      rwa [hJ] at h
    have hzU : glueU hev (Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹)) ∈ UAd hc n := by
      change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
        ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
      rw [hJ]
      exact glueU_mem _ hev hσ hgU'
    refine ⟨glueU hev (Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹)) * y, mul_mem hzU hy, ?_, ?_⟩
    · intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hwv | hw
      · rw [hwv, Units.val_mul, glueU_val, glue_smul_same hev]
        have hvT : eAt E v * eP E (fun u => u ∉ T) = eAt E v := by
          rw [hAt, hmul]
          exact eP_congr (fun u => ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact hv⟩⟩)
        have hy1 : eAt E v • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
            eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
          calc eAt E v • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
              = (eAt E v * eP E (fun u => u ∉ T)) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
                  Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by rw [hvT]
            _ = eAt E v • (eP E (fun u => u ∉ T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
                  Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [smul_smul]
            _ = eAt E v • (eP E (fun u => u ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [h2]
            _ = eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by rw [smul_smul, hvT]
        rw [← Matrix.mul_smul, hy1, Matrix.mul_smul, Matrix.mul_one]
      · have hwv : w ≠ v := fun h => hv (h ▸ hw)
        have h0 : eAt E w * eAt E v = 0 := by
          rw [hAt w, hAt v, hmul, ← eP_false]
          exact eP_congr (fun u => ⟨fun h => hwv (h.1.symm.trans h.2), False.elim⟩)
        rw [Units.val_mul, glueU_val, glue_smul_zero h0]
        exact h1 w hw
    · have hf0 : eP E (fun u => u ∉ insert v T) * eAt E v = 0 := by
        rw [hAt v, hmul, ← eP_false]
        exact eP_congr (fun u => ⟨fun h => h.1 (by rw [h.2]; exact Finset.mem_insert_self v T), False.elim⟩)
      have hff : eP E (fun u => u ∉ insert v T) * eP E (fun u => u ∉ T) = eP E (fun u => u ∉ insert v T) := by
        rw [hmul]
        exact eP_congr (fun u => ⟨fun h => h.1, fun h => ⟨h, fun hu => h (Finset.mem_insert_of_mem hu)⟩⟩)
      rw [Units.val_mul, glueU_val, glue_smul_zero hf0]
      calc eP E (fun u => u ∉ insert v T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
            Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
          = (eP E (fun u => u ∉ insert v T) * eP E (fun u => u ∉ T)) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
              Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by rw [hff]
        _ = eP E (fun u => u ∉ insert v T) • (eP E (fun u => u ∉ T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
              Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [smul_smul]
        _ = eP E (fun u => u ∉ insert v T) • (eP E (fun u => u ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
              rw [h2]
        _ = eP E (fun u => u ∉ insert v T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
              rw [smul_smul, hff]

end Formalism.L2.GenusGluing.Gen
end
end
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF, Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds, Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds, Formalism.LocalToGlobal.Columns.InputsGenus

-- ===== clump member: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF =====
-- clump-header: {"m": "Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF", "h": "module\n\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.Statement\npublic import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.Columns.AdelicLemmas\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem glEquiv_apply_lemma {n : ℕ} (γ : GL (Fin n) E) (x : Sp E n) :
    Formalism.UG.glEquiv γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := rfl

theorem asm_mem_gmap {n : ℕ} (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Sp E n)) (y : Sp E n) :
    y ∈ Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) L ↔ ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y ∈ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h
    refine ⟨_, h, ?_⟩
    rw [glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem asm_smul_mulVec {n : ℕ} (f : E ⊗[F] Formalism.L2.Herm.Af F) (M M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : f • M = f • M') (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (i : Fin n) :
    f * (M *ᵥ w) i = f * (M' *ᵥ w) i := by
  have hij : ∀ j, f * M i j = f * M' i j := fun j => by
    have hh := congrFun (congrFun h i) j
    simpa [Matrix.smul_apply, smul_eq_mul] using hh
  change f * (∑ j, M i j * w j) = f * (∑ j, M' i j * w j)
  simp only [Finset.mul_sum, ← mul_assoc, hij]

theorem asm_iota_OF (r : 𝓞 F) :
    iA F E (algebraMap (𝓞 F) E r) = iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) := by
  first
    | rfl

theorem asm_smul_apply {n : ℕ} (c : 𝓞 E) (y : Sp E n) (i : Fin n) : (c • y) i = algebraMap (𝓞 E) E c * y i := by
  show c • y i = _
  exact Algebra.smul_def c (y i)

theorem asm_mem_std {n : ℕ} (y : Sp E n) :
    y ∈ stdLat E n ↔ ∀ i, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = y i := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem asm_iota_std {n : ℕ} {y : Sp E n} (hy : y ∈ stdLat E n) (i : Fin n) : iA F E (y i) ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨b, hb⟩ := (asm_mem_std y).1 hy i
  rw [← hb]
  exact _root_.Formalism.L2.Col.iA_mem b

theorem asm_bc_mulVec {n : ℕ} (γ : GL (Fin n) E) (y : Sp E n) :
    ((Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => iA F E (y i)) = fun i => iA F E (((γ : Matrix (Fin n) (Fin n) E) *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem asm_of_mem_complF {v : HeightOneSpectrum (𝓞 F)} {s : 𝓞 E} (hs : s ∈ complF E v) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r = s := by
  unfold complF at hs
  obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hs
  exact ⟨r, hr, rfl⟩

end SlopeTestRemainingChoices

theorem locToAd_of (hG : GenusToPoint) : LocToAd := by
  intro F E _ _ _ _ _ _ hc n hL N hN hU
  exact hG F E hc n N hN (hL hc.cmUnram N hN hU)

private theorem glob_lemma_2 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {n : ℕ} (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : Sp E n) :
    y ∈ Formalism.UG.CS.globLat x (stdLat E n) ↔
      ∀ i, (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E := by
  change (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) ∈
    Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ _
  generalize (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) = w
  constructor
  · intro hw i
    let Q : Submodule (Formalism.L2.Herm.intAf F E) (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { carrier := {w | ∀ i, w i ∈ Formalism.L2.Herm.intAf F E}
        add_mem' := by
          intro a b ha hb k
          exact add_mem (ha k) (hb k)
        zero_mem' := by
          intro k
          exact zero_mem _
        smul_mem' := by
          intro c a ha k
          exact mul_mem c.2 (ha k) }
    have hle : Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ≤ Q := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨z, hz, rfl⟩ j
      exact asm_iota_std hz j
    exact (hle hw : ∀ k, w k ∈ Formalism.L2.Herm.intAf F E) i
  · intro hw
    have hsum : w = ∑ i, (⟨w i, hw i⟩ : Formalism.L2.Herm.intAf F E) •
        (fun j => iA F E ((Pi.single i (1 : E) : Fin n → E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [Subring.smul_def]
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hsum]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Pi.single i (1 : E), ?_, rfl⟩))
    refine (asm_mem_std _).2 (fun k => ⟨(Pi.single i (1 : 𝓞 E) : Fin n → 𝓞 E) k, ?_⟩)
    rcases eq_or_ne k i with rfl | h
    · simp
    · simp [h]

private theorem unit_lemma_5 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (hStd E n)) : ∃ γ ∈ URat hc n, Formalism.UG.glEquiv γ = g := by
  set γ : GL (Fin n) E := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).symm g) with hγdef
  have hγg : Formalism.UG.glEquiv γ = g := by
    simp only [Formalism.UG.glEquiv, hγdef, MulEquiv.apply_symm_apply]
  refine ⟨γ, ?_, hγg⟩
  show Formalism.UG.cT (hc.sig : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1
  rw [Matrix.mul_one]
  change (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1
  ext j k
  have h := hg (Pi.single j 1) (Pi.single k 1)
  rw [← hγg] at h
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, glEquiv_apply_lemma] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  convert h using 1
  · simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [Pi.single_apply, apply_ite star, Finset.sum_ite_eq']
    exact if_congr eq_comm rfl rfl

private theorem over_lemma_6 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ PP : HeightOneSpectrum (𝓞 E), Formalism.L2.DIV.underPl F PP = v := by
  haveI := v.isMaximal
  haveI : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
      | infer_instance
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have e : algebraMap (𝓞 F) E a = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) := by
      first
        | rfl
    rw [ha, map_zero] at e
    have e2 : algebraMap (𝓞 F) E a = algebraMap F E (algebraMap (𝓞 F) F a) := by
      first
        | rfl
    rw [e2, map_eq_zero_iff _ (algebraMap F E).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)] at e
    rw [e]
    exact zero_mem _
  obtain ⟨Q, hQ, hQv⟩ : ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
    first
      | exact Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField (K := E))
  exact ⟨⟨Q, hQ.isPrime, hQ0⟩, IsDedekindDomain.HeightOneSpectrum.ext hQv⟩

private theorem split_lemma_8 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hI : IdemCalc) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u : E ⊗[F] Formalism.L2.Herm.Af F) :
    u ∈ Formalism.L2.Herm.intAf F E ↔ (∀ v ∈ T, eAt E v * u ∈ Formalism.L2.Herm.intAf F E) ∧ eP E (fun v => v ∉ T) * u ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hu
    exact ⟨fun v _ => mul_mem ((hI F E).1 _) hu, mul_mem ((hI F E).1 _) hu⟩
  · rintro ⟨h1, h2⟩
    have e : u = ∑ v ∈ T, eAt E v * u + eP E (fun v => v ∉ T) * u := by
      rw [← Finset.sum_mul, ← add_mul, (hI F E).2.2 T, one_mul]
    rw [e]
    exact add_mem (sum_mem fun v hv => h1 v hv) h2

open Formalism.HermitianLatticesTheory in
private theorem fullLattice_of_sameGenus {E : Type} [Field E] [NumberField E] [StarRing E]
    {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hG : SameGenus (hStd E n) (stdLat E n) N) : Submodule.IsFullLattice E N := by
  refine { toIsLattice := hN, span_eq_top := ?_ }
  obtain ⟨p, hp⟩ := Ideal.exists_maximal (𝓞 E)
  let _ := hp.isPrime
  obtain ⟨g, _, hg⟩ := hG p hp
  apply (Submodule.eq_top_iff_forall_basis_mem ((Pi.basisFun E (Fin n)).map g)).2
  intro i
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  have hi : (Pi.single i (1 : E) : Sp E n) ∈ stdLat E n := by
    simpa using single_mem_stdLat (E := E) i 1
  have hgi : g (Pi.single i (1 : E)) ∈ loc (K := E) p N := by
    rw [← hg, gmap, Submodule.mem_map]
    exact ⟨_, locBasic_le_locS _ _ hi, rfl⟩
  obtain ⟨s, hs, hsi⟩ := locBasic_mem_locS.mp hgi
  have hs₀ : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h
    have hs_zero := (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp h
    exact locBasic_hcompl_not_mem (K := E) p s hs (hs_zero ▸ p.zero_mem)
  let W := Submodule.span E (N : Set (Sp E n))
  have hsmul : algebraMap (𝓞 E) E s • g (Pi.single i (1 : E)) ∈ W :=
    Submodule.subset_span (by rwa [algebraMap_smul])
  simpa only [inv_smul_smul₀ hs₀] using W.smul_mem (algebraMap (𝓞 E) E s)⁻¹ hsmul

theorem genusToPoint_of (hLoc : LocEq) (hMem : MemLocFStd) (hCof : IdemCof) (hI : IdemCalc) (hGl : GlueExists)
    (hCm : Commens) : GenusToPoint := by
  intro F E _ _ _ _ _ _ hc n N hN hG
  obtain ⟨D, hD, hD1, hD2⟩ := hCm F E n N (fullLattice_of_sameGenus hN hG)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | D ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span ({D} : Set (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hD
    exact (Ideal.finite_factors h0).subset (fun v hv => Ideal.dvd_span_singleton.2 hv)
  set T := hfin.toFinset with hT
  have memT : ∀ v, v ∈ T ↔ D ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ ∈ URat hc n,
      Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) (locF v (stdLat E n)) = locF v N := by
    intro v
    obtain ⟨PP, hPP⟩ := over_lemma_6 (E := E) v
    obtain ⟨g, hg, hgl⟩ := hG PP.asIdeal PP.isMaximal
    obtain ⟨γ, hγ, rfl⟩ := unit_lemma_5 hc g hg
    refine ⟨γ, hγ, ?_⟩
    rw [hLoc F E hc n PP, hLoc F E hc n PP, hPP] at hgl
    exact hgl
  choose γ hγ hγl using hloc
  obtain ⟨x, hx, hx1, hx2⟩ := hGl F E hc n T (fun v => ⟨γ v, hγ v⟩)
  have hx1' : ∀ v ∈ T, eAt E v • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      eAt E v • ((Formalism.UG.bc (iA F E) ((γ v)⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hx1
  have hx2' : eP E (fun v => v ∉ T) • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = eP E (fun v => v ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hx2
  refine ⟨x, hx, ?_⟩
  ext y
  rw [glob_lemma_2]
  have hTv : ∀ v ∈ T, ((∀ i, eAt E v * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E) ↔
      y ∈ locF v N) := by
    intro v hv
    rw [← hγl v, asm_mem_gmap, hMem F E n v]
    refine forall_congr' fun i => ?_
    rw [asm_smul_mulVec _ _ _ (hx1' v hv), asm_bc_mulVec]
  have hout : ∀ i, eP E (fun v => v ∉ T) * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i =
      eP E (fun v => v ∉ T) * iA F E (y i) := by
    intro i
    rw [asm_smul_mulVec _ _ _ hx2', Matrix.one_mulVec]
  have hPT : eP E (fun v => v ∉ T) = eP E (fun v : HeightOneSpectrum (𝓞 F) => D ∉ v.asIdeal) := by
    congr 1
    funext v
    rw [memT]
  constructor
  · intro hy
    have hloc' : ∀ v ∈ T, y ∈ locF v N := fun v hv =>
      (hTv v hv).1 (fun i => ((split_lemma_8 hI T _).1 (hy i)).1 v hv)
    have hout' : ∀ i, eP E (fun v => v ∉ T) * iA F E (y i) ∈ Formalism.L2.Herm.intAf F E := fun i => by
      rw [← hout i]
      exact ((split_lemma_8 hI T _).1 (hy i)).2
    let J : Ideal (𝓞 F) :=
      { carrier := {a | algebraMap (𝓞 F) (𝓞 E) a • y ∈ N}
        add_mem' := by
          intro a b ha hb
          show algebraMap (𝓞 F) (𝓞 E) (a + b) • y ∈ N
          rw [map_add (f := _), add_smul]
          exact N.add_mem ha hb
        zero_mem' := by
          show algebraMap (𝓞 F) (𝓞 E) 0 • y ∈ N
          rw [map_zero, zero_smul]
          exact N.zero_mem
        smul_mem' := by
          intro c a ha
          show algebraMap (𝓞 F) (𝓞 E) (c • a) • y ∈ N
          rw [smul_eq_mul, map_mul, mul_smul]
          exact N.smul_mem _ ha }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨Mx, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : Mx ≠ ⊥ := by
        first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField (K := F))
      let w : HeightOneSpectrum (𝓞 F) := ⟨Mx, hM.isPrime, hM0⟩
      by_cases hw : w ∈ T
      · obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ N := hloc' w hw
        obtain ⟨r, hr, rfl⟩ := asm_of_mem_complF hs
        exact hr (hJM (show r ∈ J from hsy))
      · have hyw : y ∈ locF w (stdLat E n) := by
          rw [hMem F E n w]
          intro i
          have hh := mul_mem ((hI F E).1 (fun u => u = w)) (hout' i)
          rw [← mul_assoc, (hI F E).2.1] at hh
          have e : (fun u : HeightOneSpectrum (𝓞 F) => u = w ∧ u ∉ T) = (fun u => u = w) := by
            funext u
            apply propext
            constructor
            · exact fun h => h.1
            · intro h
              refine ⟨h, ?_⟩
              rw [h]
              exact hw
          rw [e] at hh
          exact hh
        obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ stdLat E n := hyw
        obtain ⟨r, hr, rfl⟩ := asm_of_mem_complF hs
        have hDw : D ∉ w.asIdeal := fun h => hw ((memT w).2 h)
        have hmem : D * r ∈ J := by
          show algebraMap (𝓞 F) (𝓞 E) (D * r) • y ∈ N
          rw [map_mul, mul_smul]
          exact hD2 _ hsy
        exact (w.isPrime.mem_or_mem (hJM hmem)).elim hDw hr
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    have h1' : algebraMap (𝓞 F) (𝓞 E) 1 • y ∈ N := h1
    rwa [map_one, one_smul] at h1'
  · intro hy i
    rw [split_lemma_8 hI T]
    refine ⟨fun v hv => ?_, ?_⟩
    · exact (hTv v hv).2 (⟨1, (complF E v).one_mem, by rwa [one_smul]⟩ : ∃ s ∈ complF E v, s • y ∈ N) i
    · rw [hout i, hPT]
      apply hCof F E D hD
      have hh := asm_iota_std (F := F) (hD1 y hy) i
      rw [asm_smul_apply, map_mul, ← asm_iota_OF] at hh
      exact hh

end Formalism.L2.GenusGluing.Gen
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF =====

-- ===== clump member: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds =====
-- clump-header: {"m": "Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds", "h": "module\n\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists\npublic import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV
open scoped TensorProduct

section LocEqSec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

omit [NumberField F] [NumberField E] [StarRing E] in
theorem loc_coe_algebraMap (r : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (r : F) := rfl

theorem loc_hcompl_prop (PP : Pl E) (s : 𝓞 E) (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) PP.asIdeal) :
    s ∉ PP.asIdeal ∧ starO s ∉ PP.asIdeal := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    exact ⟨hx.1, hx.2 (starO x) (starO_coe x)⟩
  | one =>
    have h1 : starO (1 : 𝓞 E) = 1 := map_one (starOHom (E := E))
    rw [h1]
    exact ⟨PP.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one),
      PP.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)⟩
  | mul x y _ _ hx hy =>
    have hm : starO (x * y) = starO x * starO y := map_mul (starOHom (E := E)) x y
    rw [hm]
    exact ⟨fun h => (PP.isPrime.mem_or_mem h).elim hx.1 hy.1,
      fun h => (PP.isPrime.mem_or_mem h).elim hx.2 hy.2⟩

end LocEqSec

theorem localEquality_holds : LocEq := by
  intro F E _ _ _ _ _ _ hc n PP L
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx
    obtain ⟨hs1, hs2⟩ := loc_hcompl_prop PP s hs
    set m : 𝓞 E := s * starO s with hm
    have hfix : star ((m : 𝓞 E) : E) = (m : E) := by
      show star ((s : E) * ((starO s : 𝓞 E) : E)) = (s : E) * ((starO s : 𝓞 E) : E)
      rw [starO_coe, star_mul', star_star, mul_comm]
    obtain ⟨a, ha⟩ := (hc.fixed (m : E)).1 hfix
    have hint : IsIntegral ℤ a := by
      have h2 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact m.2
      exact (isIntegral_algebraMap_iff ).1 h2
    set r : 𝓞 F := ⟨a, hint⟩ with hr
    have hrm : algebraMap (𝓞 F) (𝓞 E) r = m := by
      apply RingOfIntegers.ext
      rw [loc_coe_algebraMap]
      exact ha
    have hmp : m ∉ PP.asIdeal := fun h => (PP.isPrime.mem_or_mem h).elim hs1 hs2
    refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨m, ⟨r, ?_, hrm⟩, ?_⟩
    · show r ∉ (underPl F PP).asIdeal
      rw [underPl_asIdeal, Ideal.mem_comap, hrm]
      exact hmp
    · rw [hm, mul_comm, mul_smul]
      exact L.smul_mem _ hsx
  · apply Formalism.HermitianLatticesTheory.locBasic_locS_le_of_le
    rintro _ ⟨r, hr, rfl⟩
    apply Submonoid.subset_closure
    have hr' : algebraMap (𝓞 F) (𝓞 E) r ∉ PP.asIdeal := by
      intro h
      apply hr
      show r ∈ (underPl F PP).asIdeal
      rw [underPl_asIdeal, Ideal.mem_comap]
      exact h
    refine ⟨hr', fun t ht htp => hr' ?_⟩
    have hfix : star (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) =
        algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) :=
      (hc.fixed _).2 ⟨(r : F), rfl⟩
    rw [hfix] at ht
    have : t = algebraMap (𝓞 F) (𝓞 E) r := FaithfulSMul.algebraMap_injective (𝓞 E) E ht
    rw [← this]
    exact htp

section CommensSec

variable {E : Type} [Field E] [NumberField E]

theorem commens_denoms (s : Finset E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ s, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (d : E) * x := by
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) s
  refine ⟨y, hy, fun x hx => ⟨⟨_, hint x hx⟩, ?_⟩⟩
  show (y • x : E) = _
  rw [zsmul_eq_mul]

end CommensSec

theorem commensurable_holds :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), Submodule.IsFullLattice E N →
      ∃ D : 𝓞 F, D ≠ 0 ∧ (∀ y ∈ N, algebraMap (𝓞 F) (𝓞 E) D • y ∈ stdLat E n) ∧
        (∀ y ∈ stdLat E n, algebraMap (𝓞 F) (𝓞 E) D • y ∈ N) := by
  intro F E _ _ _ _ _ n N hN
  classical
  let _ : Submodule.IsFullLattice E N := hN
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg E N
  obtain ⟨d1, hd1, h1⟩ := commens_denoms (s.biUnion fun x => Finset.univ.image x)
  have hA : ∀ y ∈ N, ((d1 : 𝓞 E)) • y ∈ stdLat E n := by
    have hle : N ≤ (stdLat E n).comap (((d1 : 𝓞 E)) • LinearMap.id) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [stdLat, Submodule.mem_pi]
      intro i _
      rw [Submodule.mem_one]
      obtain ⟨o, ho⟩ := h1 (x i) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
      refine ⟨o, ?_⟩
      rw [ho, Pi.smul_apply, Algebra.smul_def, map_intCast]
    intro y hy
    have := hle hy
    simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] using this
  have hB : ∀ i : Fin n, Pi.single i (1 : E) ∈ Submodule.span E (N : Set (Sp E n)) := by
    intro i
    rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := N)]
    exact Submodule.mem_top
  choose f t ht _ hsum using fun i => Submodule.mem_span_iff_exists_finset_subset.1 (hB i)
  obtain ⟨d2, hd2, h2⟩ := commens_denoms (Finset.univ.biUnion fun i => (t i).image (f i))
  have hsingle : ∀ i : Fin n, ((d2 : 𝓞 E)) • Pi.single i (1 : E) ∈ N := by
    intro i
    rw [← hsum i, Finset.smul_sum]
    apply Submodule.sum_mem
    intro a ha
    obtain ⟨o, ho⟩ := h2 (f i a) (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨a, ha, rfl⟩⟩)
    have e : ((d2 : 𝓞 E)) • (f i a • a) = o • a := by
      rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul E, smul_smul, ← ho, algebraMap_smul]
    rw [e]
    exact N.smul_mem o (ht i ha)
  have hC : ∀ y ∈ stdLat E n, ((d2 : 𝓞 E)) • y ∈ N := by
    intro y hy
    rw [stdLat, Submodule.mem_pi] at hy
    choose o ho using fun i => Submodule.mem_one.1 (hy i (Set.mem_univ i))
    have ey : y = ∑ i, o i • Pi.single i (1 : E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, ← ho j, Algebra.smul_def]
    rw [ey, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i _
    rw [smul_comm]
    exact N.smul_mem (o i) (hsingle i)
  refine ⟨((d1 * d2 : ℤ) : 𝓞 F), ?_, ?_, ?_⟩
  · exact_mod_cast mul_ne_zero hd1 hd2
  · intro y hy
    rw [map_intCast, Int.cast_mul, mul_comm, mul_smul]
    exact (stdLat E n).smul_mem _ (hA y hy)
  · intro y hy
    rw [map_intCast, Int.cast_mul, mul_smul]
    exact N.smul_mem _ (hC y hy)
end Formalism.L2.GenusGluing.Gen -- clump:auto
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds =====

-- ===== clump member: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds =====
-- clump-header: {"m": "Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds", "h": "module\n\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.Statement\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem glueExists_holds : GlueExists := glueExists_of idempotentCalculation_holds

theorem genusToPoint_holds : GenusToPoint :=
  genusToPoint_of localEquality_holds memLocalizedStd_holds idempotentCofinite_holds idempotentCalculation_holds glueExists_holds commensurable_holds

theorem localToAdelic_holds : LocToAd := locToAd_of genusToPoint_holds

end Formalism.L2.GenusGluing.Gen
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds =====

-- ===== clump member: Formalism.LocalToGlobal.Columns.InputsGenus =====
-- clump-header: {"m": "Formalism.LocalToGlobal.Columns.InputsGenus", "h": "module\n\npublic import Formalism.LocalToGlobal.Columns.Inputs\npublic import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds\npublic import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.Col

open NumberField

theorem unimodGenusLocAll_holds : UnimodGenusLocAll := unimodular_genus_unique

theorem unimodGenusLoc_holds (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : UnimodGenusLoc E n :=
  unimodGenusLocAll_holds E n

theorem unimodGenus_holds {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] : UnimodGenus hc n :=
  Formalism.L2.GenusGluing.Gen.localToAdelic_holds F E hc n (unimodGenusLoc_holds E n)

end Formalism.L2.Col
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.Columns.InputsGenus =====
