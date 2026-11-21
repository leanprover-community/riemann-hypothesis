import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoClose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.HformEntry
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.HformSmulLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StFix
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.ExistsOrthogonalFamily

section
noncomputable section

namespace PI.VolStabW

theorem exStab_of_orb (hO : OrbTup) (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW.OrbR

open Matrix Formalism.UG PIW.AdelicOrbitU

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

def r1 (c : S) (u v : Fin n → S) : Matrix (Fin n) (Fin n) S :=
  1 - c • vecMulVec v (vecMul (fun i => s (u i)) J)

theorem reflection_mulVec (c : S) (u v z : Fin n → S) :
    r1 s J c u v *ᵥ z = z - (c * hform s J u z) • v := by
  rw [r1, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    ← hform_eq_dot, op_smul_eq_smul, smul_smul]

theorem hform_mulVec (T : Matrix (Fin n) (Fin n) S) (z w : Fin n → S) :
    hform s J (T *ᵥ z) (T *ᵥ w) = hform s (cT s T * J * T) z w := by
  rw [hform_eq_dot, hform_eq_dot]
  have e : (fun i => s ((T *ᵥ z) i)) = T.map s *ᵥ (fun i => s (z i)) := by
    funext i; exact RingHom.map_mulVec s T z i
  rw [e, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rfl

theorem hform_mem (g : GL (Fin n) S) (hg : g ∈ UJ s J) (z w : Fin n → S) :
    hform s J ((g : Matrix (Fin n) (Fin n) S) *ᵥ z) ((g : Matrix (Fin n) (Fin n) S) *ᵥ w) =
      hform s J z w := by
  have hg' : cT s (g : Matrix (Fin n) (Fin n) S) * J * (g : Matrix (Fin n) (Fin n) S) = J := hg
  rw [hform_mulVec, hg']

theorem mem_UJ_of (hdet : IsUnit J.det) (T : Matrix (Fin n) (Fin n) S)
    (key : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) = T := by
  have hM : cT s T * J * T = J := by
    ext i j
    rw [hform_entry, key, hform_single]
  have hL : (J⁻¹ * cT s T * J) * T = 1 := by
    calc (J⁻¹ * cT s T * J) * T = J⁻¹ * (cT s T * J * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, nonsing_inv_mul _ hdet]
  have hR : T * (J⁻¹ * cT s T * J) = 1 := mul_eq_one_comm.mp hL
  exact ⟨⟨T, J⁻¹ * cT s T * J, hR, hL⟩, hM, rfl⟩

theorem step (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det)
    (a b : Fin n → S) (hab : hform s J b b = hform s J a a) (hu : IsUnit (hform s J a a))
    (lam : S) (hlam : lam * s lam = 1) (hc : IsUnit (hform s J a a - s lam * hform s J b a)) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) *ᵥ a = b ∧
      ∀ z, hform s J a z = 0 → hform s J b z = 0 → (g : Matrix (Fin n) (Fin n) S) *ᵥ z = z := by
  have hconj := hform_conj s J hs hJ
  obtain ⟨c, hc_def⟩ : ∃ c, hform s J a a - s lam * hform s J b a = c := ⟨_, rfl⟩
  rw [hc_def] at hc
  obtain ⟨ci, hci⟩ : ∃ ci, c * ci = 1 := hc.exists_right_inv
  have e2 : ci * c = 1 := by rw [mul_comm]; exact hci
  have e3 : s ci * s c = 1 := by rw [← map_mul, e2, map_one]
  obtain ⟨u, hu_def⟩ : ∃ u, a - lam • b = u := ⟨_, rfl⟩
  have hua : hform s J u a = c := by
    rw [← hu_def, hform_sub_left, hform_smul_left, hc_def]
  have huu : hform s J u u = c + s c := by
    rw [← hu_def, ← hc_def]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_sub, map_mul,
      hs, hconj]
    linear_combination (s lam * lam) * hab + hform s J a a * hlam
  have key1 : ∀ z w, hform s J (r1 s J ci u u *ᵥ z) (r1 s J ci u u *ᵥ w) = hform s J z w := by
    intro z w
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_mul, hconj, huu]
    linear_combination (hform s J z u * hform s J u w * s ci) * e2 +
      (hform s J z u * hform s J u w * ci) * e3
  obtain ⟨g1, hg1U, hg1⟩ := mem_UJ_of s J hdet _ key1
  obtain ⟨βi, hβ⟩ : ∃ βi, hform s J a a * βi = 1 := hu.exists_right_inv
  have hsβ : s (hform s J a a) = hform s J a a := hconj a a
  have hsβi : s βi = βi := by
    have h1 : hform s J a a * s βi = 1 := by rw [← hsβ, ← map_mul, hβ, map_one]
    calc s βi = s βi * (hform s J a a * βi) := by rw [hβ, mul_one]
      _ = (hform s J a a * s βi) * βi := by ring
      _ = βi := by rw [h1, one_mul]
  have key2 : ∀ z w, hform s J (r1 s J ((1 - s lam) * βi) b b *ᵥ z)
      (r1 s J ((1 - s lam) * βi) b b *ᵥ w) = hform s J z w := by
    intro z w
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_mul, hconj, hab,
      map_sub, map_one, hs, hsβi]
    linear_combination (hform s J z b * hform s J b w * βi) * hlam +
      (hform s J z b * hform s J b w * (1 - lam) * (1 - s lam) * βi) * hβ
  obtain ⟨g2, hg2U, hg2⟩ := mem_UJ_of s J hdet _ key2
  refine ⟨g2 * g1, mul_mem hg2U hg1U, ?_, ?_⟩
  · rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2, reflection_mulVec s J ci u u, hua, e2, one_smul, ← hu_def,
      sub_sub_cancel, reflection_mulVec, hform_smul_right, hab, ← sub_smul]
    conv_rhs => rw [← one_smul S b]
    congr 1
    linear_combination hlam + (s lam * lam - lam) * hβ
  · intro z hz1 hz2
    have hzu : hform s J u z = 0 := by
      rw [← hu_def, hform_sub_left, hform_smul_left, hz1, hz2, mul_zero, sub_zero]
    rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2, reflection_mulVec s J ci u u, hzu, mul_zero, zero_smul, sub_zero,
      reflection_mulVec, hz2, mul_zero, zero_smul, sub_zero]

theorem orb_orth (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det) :
    ∀ (k : ℕ) (x y : Fin k → Fin n → S), (∀ i j, i ≠ j → hform s J (x i) (x j) = 0) →
      (∀ i j, hform s J (y i) (y j) = hform s J (x i) (x j)) →
      (∀ i, IsUnit (hform s J (x i) (x i))) →
      (∀ i (t : S), ∃ lam, lam * s lam = 1 ∧ IsUnit (hform s J (x i) (x i) - s lam * t)) →
      ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ x i = y i := by
  intro k
  induction k with
  | zero => intro x y _ _ _ _; exact ⟨1, one_mem _, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro x y ho hg hu hl
    obtain ⟨g', hg'U, hg'⟩ := ih (fun i => x i.succ) (fun i => y i.succ)
      (fun i j hij => ho _ _ (fun e => hij (Fin.succ_injective _ e))) (fun i j => hg _ _)
      (fun i => hu _) (fun i t => hl _ t)
    obtain ⟨a, ha⟩ : ∃ a, (g' : Matrix (Fin n) (Fin n) S) *ᵥ x 0 = a := ⟨_, rfl⟩
    have haa : hform s J a a = hform s J (x 0) (x 0) := by rw [← ha]; exact hform_mem s J g' hg'U _ _
    obtain ⟨lam, hlam, hc⟩ := hl 0 (hform s J (y 0) a)
    rw [← haa] at hc
    obtain ⟨g1, hg1U, hg1a, hg1z⟩ := step s J hs hJ hdet a (y 0) (by rw [haa]; exact hg 0 0)
      (haa ▸ hu 0) lam hlam hc
    refine ⟨g1 * g', mul_mem hg1U hg'U, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Units.val_mul, ← mulVec_mulVec, ha]; exact hg1a
    · have hi := hg' i
      rw [Units.val_mul, ← mulVec_mulVec, hi]
      apply hg1z
      · rw [← hi, ← ha, hform_mem s J g' hg'U]; exact ho 0 i.succ (Fin.succ_ne_zero i).symm
      · rw [hg 0 i.succ]; exact ho 0 i.succ (Fin.succ_ne_zero i).symm

def tM {m : ℕ} (X : Fin m → Fin n → S) : Matrix (Fin n) (Fin m) S := Matrix.of fun r i => X i r

theorem gram_tM {m : ℕ} (X : Fin m → Fin n → S) (i j : Fin m) :
    hform s J (X i) (X j) = (cT s (tM X) * J * tM X) i j := by
  simp only [hform, cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, tM, Matrix.of_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem gram_mul {m k : ℕ} (N : Matrix (Fin n) (Fin m) S) (Q : Matrix (Fin m) (Fin k) S) :
    cT s (N * Q) * J * (N * Q) = cT s Q * (cT s N * J * N) * Q := by
  rw [cT_mul]; simp only [Matrix.mul_assoc]

end PI.VolStabW.OrbR
end
end

section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabW.OrbR
open scoped TensorProduct

theorem cm_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ a = a ↔ a ∈ (algebraMap F E).range := by
  constructor
  · intro ha
    by_contra hn
    have hli : LinearIndependent F ![(1 : E), a] := by
      rw [LinearIndependent.pair_iff]
      intro p q hpq
      by_cases hq : q = 0
      · subst hq
        simp only [zero_smul, add_zero] at hpq
        exact ⟨by simpa using hpq, rfl⟩
      · exfalso
        apply hn
        refine ⟨-(p / q), ?_⟩
        have e : q • a = -(p • (1 : E)) := by linear_combination hpq
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
        have hq' : algebraMap F E q ≠ 0 := by simpa using hq
        rw [map_neg, map_div₀]
        field_simp
        linear_combination -e
    have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
    let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hid : σ.toLinearMap = LinearMap.id := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp [b]
      · simp [b, ha]
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hreal : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have e1 := h.2.2.2 τ x
      have e2 : σ x = x := by
        have := congrArg (fun f : E →ₗ[F] E => f x) hid
        simpa using this
      rw [e2] at e1
      rw [starRingEnd_apply, ← e1]
    have hc := h.2.1.isComplex (InfinitePlace.mk τ)
    exact (InfinitePlace.not_isComplex_iff_isReal.mpr ⟨τ, hreal, rfl⟩) hc
  · rintro ⟨b, rfl⟩; exact σ.commutes b

theorem orbTup_holds : OrbTup := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet y hy
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hfix := cm_fixed σ hCM
  set T := gramE σ J X0 with hTdef
  let sE : E →+* E := σ
  have hTH : IsHerm sE T := by
    ext i j; exact hT i j
  have hh : PI.UnitaryGroupMassFormula.HermConj.IsHermForm sE (hform sE T) :=
    { add := fun x y z => by
        rw [PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot,
          PIW.AdelicOrbitU.hform_eq_dot, mulVec_add, dotProduct_add]
      smul := fun x c y => PIW.AdelicOrbitU.hform_smul_right sE T c x y
      herm := fun x y => (PIW.AdelicOrbitU.hform_conj sE T hinv hTH x y).symm }
  obtain ⟨v, hvli, hvo⟩ := PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family sE a (Fin a → E)
    (by simp) (hform sE T) hh
  set P : Matrix (Fin a) (Fin a) E := tM v with hP
  have hPu : IsUnit P.det := by
    have h1 : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.mp hvli
    have h2 : P = (Matrix.of v)ᵀ := rfl
    rw [h2, det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h1
  set D := cT sE P * T * P with hD
  have hDv : ∀ j k, hform sE T (v j) (v k) = D j k := fun j k => gram_tM sE T v j k
  have hDoff : ∀ j k, j ≠ k → D j k = 0 := fun j k hjk => by rw [← hDv]; exact hvo j k hjk
  have hDdiag : D = Matrix.diagonal fun j => D j j := by
    ext j k
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [hDoff j k hjk, Matrix.diagonal_apply_ne _ hjk]
  have hDdet : D.det ≠ 0 := by
    have hc : (cT sE P).det = sE P.det := by
      rw [cT, det_transpose, RingHom.map_det]; rfl
    rw [hD, det_mul, det_mul, hc]
    refine mul_ne_zero (mul_ne_zero ?_ hdet) hPu.ne_zero
    exact (map_ne_zero sE).mpr hPu.ne_zero
  have hDne : ∀ j, D j j ≠ 0 := by
    intro j
    rw [hDdiag, det_diagonal] at hDdet
    exact Finset.prod_ne_zero_iff.mp hDdet j (Finset.mem_univ j)
  have hDfix : ∀ j, σ (D j j) = D j j := fun j => by
    rw [← hDv]; exact PIW.AdelicOrbitU.hform_conj sE T hinv hTH _ _

  let R := AF F
  let sS := sigR R σ
  let JS := JR (F := F) R J
  have hsS : ∀ z, sS (sS z) = z := (PIW.AdelicOrbitU.stFix F E σ h2 hfix R).1
  have hJS : IsHerm sS JS := PIW.AdelicOrbitU.isHerm_JR R σ J hJ.1
  have hJSd : IsUnit JS.det := PIW.AdelicOrbitU.isUnit_det_JR (F := F) R J hJ.2
  have hcTmap : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) E),
      cT sS (N.map (inclR (F := F) R)) = (cT sE N).map (inclR (F := F) R) := by
    intro p q N; ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
    exact PIW.AdelicOrbitU.sigR_inclR (F := F) R σ _
  set Xm : Matrix (Fin M) (Fin a) (R ⊗[F] E) := (tM X0).map (inclR (F := F) R) with hXm
  set Pm : Matrix (Fin a) (Fin a) (R ⊗[F] E) := P.map (inclR (F := F) R) with hPm
  have hTg : cT sE (tM X0) * J * tM X0 = T := by
    ext i j; rw [← gram_tM]; rfl
  have hyg : cT sS (tM y) * JS * tM y = T.map (inclR (F := F) R) := by
    ext i j; rw [← gram_tM]; exact congrFun (congrFun hy i) j
  let x' : Fin a → Fin M → R ⊗[F] E := fun j r => (Xm * Pm) r j
  let y' : Fin a → Fin M → R ⊗[F] E := fun j r => (tM y * Pm) r j
  have hGx : ∀ j k, hform sS JS (x' j) (x' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM x' = Xm * Pm := rfl
    rw [e, gram_mul, hXm, hPm, hcTmap, hcTmap]
    show ((cT sE P).map (inclR (F := F) R) * ((cT sE (tM X0)).map (inclR (F := F) R) * J.map (inclR (F := F) R) *
      (tM X0).map (inclR (F := F) R)) * P.map (inclR (F := F) R)) j k = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hTg]
    rfl
  have hGy : ∀ j k, hform sS JS (y' j) (y' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM y' = tM y * Pm := rfl
    rw [e, gram_mul, hyg, hPm, hcTmap, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  obtain ⟨g, hgU, hgx⟩ := orb_orth sS JS hsS hJS hJSd a x' y'
    (fun j k hjk => by rw [hGx, hDoff j k hjk, map_zero])
    (fun j k => by rw [hGx, hGy])
    (fun j => by rw [hGx]; exact (isUnit_iff_ne_zero.mpr (hDne j)).map _)
    (fun j t => by
      obtain ⟨β, hβ⟩ := (hfix _).mp (hDfix j)
      have hβ0 : β ≠ 0 := by
        rintro rfl; exact hDne j (by rw [← hβ, map_zero])
      obtain ⟨lam, hlam, hu⟩ := PIW.AdelicOrbitU.stLam F E σ h2 hfix R (PIW.AdelicOrbitU.stP F) t β hβ0
      refine ⟨lam, hlam, ?_⟩
      rw [hGx, ← hβ, PIW.AdelicOrbitU.inclR_algebraMap]
      exact hu)
  have hmat : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm * Pm = tM y * Pm := by
    ext r j
    rw [Matrix.mul_assoc]
    have := congrFun (hgx j) r
    simpa [x', y', Matrix.mul_apply, mulVec, dotProduct] using this
  have hPmu : IsUnit Pm.det := by
    show IsUnit ((inclR (F := F) R).mapMatrix P).det
    rw [← RingHom.map_det]; exact hPu.map _
  have hmat2 : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm = tM y := by
    have := congrArg (fun N => N * Pm⁻¹) hmat
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hPmu] using this
  refine ⟨(⟨g, hgU⟩ : HR (AF F) σ J), ?_⟩
  funext i
  funext r
  show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (AF F) X0 i) r = y i r
  have := congrFun (congrFun hmat2 r) i
  simpa [Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct] using this

end PI.VolStabW
end
end

section
namespace PI.VolStabW

theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabW
end
