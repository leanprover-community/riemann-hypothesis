import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRMulNe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProofSimp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GenericNoetherNormalisation

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => 2 + f.totalDegree

local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

noncomputable abbrev nagata (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

omit [IsDomain A] in
theorem nagata_comp_neg (c : A) : (nagata f c).comp (nagata f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

noncomputable abbrev nagataEquiv := AlgEquiv.ofAlgHom (nagata f 1) (nagata f (-1))
  (nagata_comp_neg f 1) (by simpa using nagata_comp_neg f (-1))

omit [IsDomain A] in
variable {f v} in
theorem lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

theorem sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x :=
  by apply _root_.UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne <;> assumption





end Nagata

section Combination

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}

def CombAfterPower (c : A) (z : Fin m → D) (s : Finset D) (d : D) : Prop :=
  ∃ (k : ℕ) (cf : D → MvPolynomial (Fin m) A), c ^ k • d = ∑ t ∈ s, aeval z (cf t) * t

variable {c : A} {z : Fin m → D} {s : Finset D}

theorem smul_sum_aeval (b : A) (cf : D → MvPolynomial (Fin m) A) :
    b • ∑ t ∈ s, aeval z (cf t) * t = ∑ t ∈ s, aeval z (MvPolynomial.C b * cf t) * t := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_mul, MvPolynomial.aeval_C, Algebra.smul_def, mul_assoc]

theorem CombAfterPower.zero : CombAfterPower c z s 0 :=
  ⟨0, fun _ ↦ 0, by simp⟩

theorem CombAfterPower.add {d e : D} (hd : CombAfterPower c z s d) (he : CombAfterPower c z s e) :
    CombAfterPower c z s (d + e) := by
  obtain ⟨k, f, hf⟩ := hd
  obtain ⟨l, g, hg⟩ := he
  refine ⟨k + l, fun t ↦ MvPolynomial.C (c ^ l) * f t + MvPolynomial.C (c ^ k) * g t, ?_⟩
  have h1 : c ^ (k + l) • d = c ^ l • (c ^ k • d) := by rw [smul_smul, ← pow_add, add_comm]
  have h2 : c ^ (k + l) • e = c ^ k • (c ^ l • e) := by rw [smul_smul, ← pow_add]
  rw [smul_add, h1, h2, hf, hg, smul_sum_aeval, smul_sum_aeval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_add, add_mul]

theorem CombAfterPower.mul_left (P : MvPolynomial (Fin m) A) {d : D} (hd : CombAfterPower c z s d) :
    CombAfterPower c z s (aeval z P * d) := by
  obtain ⟨k, f, hf⟩ := hd
  refine ⟨k, fun t ↦ P * f t, ?_⟩
  rw [← mul_smul_comm, hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_mul, mul_assoc]

theorem CombAfterPower.sum {ι : Type*} (u : Finset ι) (F : ι → D)
    (h : ∀ i ∈ u, CombAfterPower c z s (F i)) : CombAfterPower c z s (∑ i ∈ u, F i) :=
  Finset.sum_induction _ _ (fun _ _ ↦ CombAfterPower.add) CombAfterPower.zero h

theorem CombAfterPower.of_smul {d : D} (h : CombAfterPower c z s (c • d)) :
    CombAfterPower c z s d := by
  obtain ⟨k, f, hf⟩ := h
  exact ⟨k + 1, f, by rw [pow_succ, mul_smul, hf]⟩

theorem CombAfterPower.of_mem {t : D} (ht : t ∈ s) : CombAfterPower c z s t := by
  classical
  refine ⟨0, fun u ↦ if u = t then 1 else 0, ?_⟩
  rw [pow_zero, one_smul, Finset.sum_eq_single t (fun b _ hb ↦ by simp [hb]) (fun h ↦ absurd ht h)]
  simp


end Combination

theorem algHom_eq_eval₂_finSuccEquiv {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {n : ℕ}
    (ψ : MvPolynomial (Fin (n + 1)) A →ₐ[A] D) (P : MvPolynomial (Fin (n + 1)) A) :
    ψ P = (finSuccEquiv A n P).eval₂
      (MvPolynomial.aeval (R := A) (fun i : Fin n ↦ ψ (X i.succ))).toRingHom (ψ (X 0)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add P Q hP hQ => rw [map_add, map_add, Polynomial.eval₂_add, hP, hQ]
  | mul_X P i ih =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, ih]
    congr 1
    cases i using Fin.cases <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]

universe u

theorem proof : GenericNoetherNormalisation.Statement.{u} :=
  _root_.UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof

end GenericNoetherNormalisation

end GroundTheory.Heights₂.Heights
