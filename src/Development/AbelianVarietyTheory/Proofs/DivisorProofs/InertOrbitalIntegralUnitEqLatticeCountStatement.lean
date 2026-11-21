import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeStandardHermitianStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersIffBoundedEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixIffBoundedPowers

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.SelfDualLat

theorem stdH_eq_dot (K : UQ) {n : ℕ} (a b : Fin n → K.E) :
    stdH K n a b = a ⬝ᵥ (fun k => K.c (b k)) := rfl

theorem stdH_mulVec (K : UQ) {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E)
    (hP : Pᵀ * P.map K.c = 1) (u v : Fin n → K.E) :
    stdH K n (P *ᵥ u) (P *ᵥ v) = stdH K n u v := by
  have hv : (fun k => K.c ((P *ᵥ v) k)) = P.map K.c *ᵥ (fun k => K.c (v k)) := by
    funext k
    exact RingHom.map_mulVec (K.c : K.E →+* K.E) P v k
  rw [stdH_eq_dot, stdH_eq_dot, hv, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hP, vecMul_one]

theorem intVec_eq_range (K : UQ) (n : ℕ) :
    intVec K n = LinearMap.range ((Algebra.linearMap K.O K.E).compLeft (Fin n)) := by
  ext v
  constructor
  · intro hv
    have h := fun i => RingHom.mem_range.mp (hv i)
    choose o ho using h
    exact ⟨o, funext fun i => ho i⟩
  · rintro ⟨o, rfl⟩ i
    exact ⟨o i, rfl⟩

theorem intVec_fg (K : UQ) (n : ℕ) : (intVec K n).FG := by
  rw [intVec_eq_range, LinearMap.range_eq_map]
  exact Submodule.FG.map _ Module.Finite.fg_top

theorem single_mem_intVec (K : UQ) {n : ℕ} (i : Fin n) : (Pi.single i (1 : K.E) : Fin n → K.E) ∈ intVec K n := by
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem unitLat_isLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  intro E _ _ _ _ w hns K e he hint n B ψ x hx hψ q
  set Qm : Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  have hmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := by
    intro g hg
    simpa [UL, hns] using hg
  have hQ : cT (cj w) Qm * 1 * Qm = 1 := hmem _ (q⁻¹).2
  have h2 : (Qm.map (cj w))ᵀ * Qm = 1 := by simpa [cT] using hQ
  set P : Matrix (Fin n) (Fin n) K.E := Qm.map e.symm with hPdef
  have hPc : P.map K.c = (Qm.map (cj w)).map e.symm := by
    ext i j
    apply e.injective
    simp [hPdef, he]
  have hP1 : (P.map K.c)ᵀ * P = 1 := by
    have h3 := congrArg (e.symm.toRingHom.mapMatrix) h2
    simp only [map_mul, map_one, RingHom.mapMatrix_apply] at h3
    rw [hPc, hPdef, ← Matrix.transpose_map]
    simpa using h3
  have hPR : P * (P.map K.c)ᵀ = 1 := mul_eq_one_comm.mp hP1
  have hPT : Pᵀ * P.map K.c = 1 := by
    have h4 := congrArg Matrix.transpose hP1
    simpa [Matrix.transpose_mul] using h4
  let G : (Fin n → K.E) →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' (P.map K.c)ᵀ
  have hGP : ∀ y, G (P *ᵥ ψ y) = y := by
    intro y
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hP1]
  have hPG : ∀ a, P *ᵥ ψ (G a) = a := by
    intro a
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hPR]
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ P *ᵥ ψ y ∈ intVec K n := fun y => Iff.rfl
  have hmap : unitLat e B ψ q = (intVec K n).map (G.restrictScalars K.O) := by
    ext y
    rw [hmemL]
    constructor
    · intro hy
      exact ⟨P *ᵥ ψ y, hy, hGP y⟩
    · rintro ⟨a, ha, rfl⟩
      rw [LinearMap.restrictScalars_apply, hPG]
      exact ha
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hmap]
    exact (intVec_fg K n).map _
  · rw [eq_top_iff]
    have key : Submodule.map G ⊤ ≤ Submodule.span K.E (unitLat e B ψ q : Set B.A) := by
      rw [← (Pi.basisFun K.E (Fin n)).span_eq, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      apply Submodule.subset_span
      show G _ ∈ unitLat e B ψ q
      rw [hmemL, Pi.basisFun_apply, hPG]
      exact single_mem_intVec K i
    intro y _
    rw [← hGP y]
    exact key (Submodule.mem_map_of_mem trivial)
  · intro y
    rw [hmemL]
    constructor
    · intro hy z hz
      rw [hmemL] at hz
      rw [← hψ, ← stdH_mulVec K P hPT]
      unfold stdH
      apply Subring.sum_mem
      intro k _
      apply Subring.mul_mem _ (hy k)
      obtain ⟨o, ho⟩ := hz k
      obtain ⟨o', ho'⟩ := K.c_int o
      exact ⟨o', by rw [← ho, ho']⟩
    · intro h i
      have h5 := h (G (Pi.single i 1)) (by rw [hmemL, hPG]; exact single_mem_intVec K i)
      rw [← hψ, ← stdH_mulVec K P hPT, hPG] at h5
      simpa [stdH, Pi.single_apply, apply_ite] using h5

end GlobalTheory.InertUnitOrb.SelfDualLat
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLattice_isLattice_selfDual_hermitianModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  first | exact @GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | exact GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | (intros; apply GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mulVec_int_iff {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    (∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((M *ᵥ v) i) ≤ 1) ↔
      ∀ i j, Valued.v (M i j) ≤ 1 := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single] using this
  · intro h v hv i
    rw [hmem]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ ((hmem _).1 (h i k)) ((hmem _).1 (hv k))

theorem mem_KGL_of_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (M : GLw n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w n := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h1 i j)⟩
  let N' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h2 i j)⟩
  have hinj : Function.Injective ((Formalism.UG.Ov E w).subtype.mapMatrix :
      Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) →+* Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro a b hab
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  have hN : (Formalism.UG.Ov E w).subtype.mapMatrix N = (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  have hN' : (Formalism.UG.Ov E w).subtype.mapMatrix N' = ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  refine ⟨⟨N, N', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hN, hN', map_one]; exact M.mul_inv
  · rw [map_mul, hN, hN', map_one]; exact M.inv_mul
  · apply Units.ext
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe]
    exact hN

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mem_KGL_of_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) {n : ℕ} (w : Pl E)
    (hw : ¬ IsSplitAt w) (M : GLw n w) (hM : M ∈ UL n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w n := by
  have hcj := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  rw [UL, if_neg hw] at hM
  have hM' : Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := hM
  have hinv : ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    have := congrArg (· * ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hM'
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv] at this
    exact this.symm
  refine mem_KGL_of_int w M h1 fun i j => ?_
  rw [hinv]
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hcj]
  exact h1 j i

theorem e_mulVec {K F : Type} [Field K] [Field F] (e : K ≃+* F) {n : ℕ} (Q : Matrix (Fin n) (Fin n) F)
    (u : Fin n → K) (i : Fin n) : e ((Q.map e.symm *ᵥ u) i) = (Q *ᵥ fun j => e (u j)) i := by
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  intro E _ _ _ hU w hw K e _ hint n B ψ γ hg q
  let ψ' : B.A → Fin n → w.adicCompletion E := fun y i => e (ψ y i)
  have hsurj : Function.Surjective ψ' := fun u => ⟨ψ.symm fun i => e.symm (u i), by funext i; simp [ψ']⟩
  set Qi := (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQi
  set Qm := (((q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  set Gm := (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hGm
  set Mm := (((q⁻¹ * γ * q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hMm'
  have hMm : Mm = Qi * Gm * Qm := rfl
  have hQiQm : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hQmQi : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ ∀ i, Valued.v ((Qi *ᵥ ψ' y) i) ≤ 1 := by
    intro y
    show (∀ i, ((Qi.map e.symm) *ᵥ ψ y) i ∈ (algebraMap K.O K.E).range) ↔ _
    refine forall_congr' fun i => ?_
    rw [hint, e_mulVec]
  have hgψ : ∀ y, ψ' (B.g * y) = Gm *ᵥ ψ' y := by
    intro y; funext i
    simp only [ψ']
    rw [hg, e_mulVec]
  have hstab : (∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((Mm *ᵥ v) i) ≤ 1 := by
    constructor
    · intro hst v hv
      obtain ⟨y, hy⟩ := hsurj (Qm *ᵥ v)
      have hyL : y ∈ unitLat e B ψ q := (hmemL y).2 (by rw [hy, Matrix.mulVec_mulVec, hQiQm, Matrix.one_mulVec]; exact hv)
      have := (hmemL _).1 (hst y hyL)
      rw [hgψ, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
      rw [hMm]; exact this
    · intro h y hy
      rw [hmemL] at hy ⊢
      rw [hgψ]
      have key : Qi *ᵥ (Gm *ᵥ ψ' y) = Mm *ᵥ (Qi *ᵥ ψ' y) := by
        simp only [hMm, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQmQi, Matrix.mul_one]
      rw [key]
      exact h _ hy
  rw [hstab, mulVec_int_iff, KL, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact mem_KGL_of_unitary hU w hw _ (q⁻¹ * γ * q).2 h
  · rintro ⟨N, hN⟩ i j
    have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
    rw [hmem, hMm', ← hN]
    exact ((N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w)) i j).2

end GlobalTheory.InertUnitOrb.LatStable
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLattice_stable_iff_conj_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  first | exact @GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | exact GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | (intros; apply GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitLat

theorem mulVec_int_iff {K : UQ} {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E) :
    (∀ u : Fin n → K.E, (∀ i, u i ∈ (algebraMap K.O K.E).range) →
      ∀ i, (P *ᵥ u) i ∈ (algebraMap K.O K.E).range) ↔
    ∀ i j, P i j ∈ (algebraMap K.O K.E).range := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simpa using Subring.one_mem _
      · simpa [hk] using Subring.zero_mem _) i
    simpa [Matrix.mulVec_single] using this
  · intro h u hu i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hu j)

theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := by
  intro E _ _ _ _ w _ K e _ hint n B ψ q q'
  let R := (algebraMap K.O K.E).range
  let M : GLw n w → Matrix (Fin n) (Fin n) K.E := fun g => (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm
  have hMmul : ∀ g h : GLw n w, M (g * h) = M g * M h := fun g h => by
    simp only [M, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hM1 : M 1 = 1 := by
    simp only [M, Units.val_one]
    exact Matrix.map_one (f := e.symm) (map_zero _) (map_one _)
  have hent : ∀ g : GLw n w, (∀ i j, M g i j ∈ R) ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w := by
    intro g
    refine forall_congr' fun i => forall_congr' fun j => ?_
    show e.symm _ ∈ R ↔ _
    rw [hint, RingEquiv.apply_symm_apply]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hmem : ∀ g : UL n w, ∀ y, y ∈ unitLat e B ψ g ↔ ∀ i, (M ((g : GLw n w)⁻¹) *ᵥ ψ y) i ∈ R :=
    fun g y => Iff.rfl

  have hlat : unitLat e B ψ q = unitLat e B ψ q' ↔
      ∀ v : Fin n → K.E, ((∀ i, (M ((q : GLw n w)⁻¹) *ᵥ v) i ∈ R) ↔ ∀ i, (M ((q' : GLw n w)⁻¹) *ᵥ v) i ∈ R) := by
    rw [SetLike.ext_iff]
    constructor
    · intro h v
      have := h (ψ.symm v)
      rwa [hmem, hmem, LinearEquiv.apply_symm_apply] at this
    · intro h y
      rw [hmem, hmem]
      exact h (ψ y)

  have half : ∀ a b : GLw n w,
      (∀ v : Fin n → K.E, (∀ i, (M b⁻¹ *ᵥ v) i ∈ R) → ∀ i, (M a⁻¹ *ᵥ v) i ∈ R) ↔
      ∀ i j, M (a⁻¹ * b) i j ∈ R := by
    intro a b
    rw [← mulVec_int_iff]
    constructor
    · intro h u hu
      have h1 := h (M b *ᵥ u) (by
        rw [Matrix.mulVec_mulVec, ← hMmul, inv_mul_cancel, hM1, Matrix.one_mulVec]; exact hu)
      rwa [Matrix.mulVec_mulVec, ← hMmul] at h1
    · intro h v hv
      have h1 := h _ hv
      rwa [Matrix.mulVec_mulVec, ← hMmul, mul_assoc, mul_inv_cancel, mul_one] at h1
  have hKL : q⁻¹ * q' ∈ KL n w ↔
      ((q : GLw n w)⁻¹ * q') ∈ Formalism.UG.GLint (Fin n) (Ov E w) := by
    rw [KL, Subgroup.mem_subgroupOf]
    rfl
  rw [hKL, Formalism.UG.P.tjcosets_mem_K_iff, ← hent, ← hent, hlat]
  have hinv : ((q : GLw n w)⁻¹ * q')⁻¹ = (q' : GLw n w)⁻¹ * q := by group
  rw [hinv, ← half, ← half]
  constructor
  · intro h
    exact ⟨fun v hv => (h v).2 hv, fun v hv => (h v).1 hv⟩
  · intro h v
    exact ⟨h.2 v, h.1 v⟩

end GlobalTheory.InertUnitLat
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLattice_eq_iff_inv_mul_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := by
  first | exact @GlobalTheory.InertUnitLat.unitLat_eq_iff | exact GlobalTheory.InertUnitLat.unitLat_eq_iff | (intros; apply GlobalTheory.InertUnitLat.unitLat_eq_iff <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.CentTorusModel

variable {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))

def mulMat (a : B.A) : Matrix (Fin n) (Fin n) K.E :=
  LinearMap.toMatrix' (ψ.toLinearMap ∘ₗ LinearMap.mulLeft K.E a ∘ₗ ψ.symm.toLinearMap)

theorem mulMat_mulVec (a y : B.A) : mulMat B ψ a *ᵥ ψ y = ψ (a * y) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem eq_mulMat {M : Matrix (Fin n) (Fin n) K.E} {a : B.A} (h : ∀ y, M *ᵥ ψ y = ψ (a * y)) :
    M = mulMat B ψ a := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨y, rfl⟩ := ψ.surjective v
  simp only [Matrix.toLin'_apply, h, mulMat_mulVec]

theorem mulMat_one : mulMat B ψ 1 = 1 :=
  (eq_mulMat B ψ (fun y => by simp)).symm

theorem mulMat_mul (a b : B.A) : mulMat B ψ (a * b) = mulMat B ψ a * mulMat B ψ b :=
  (eq_mulMat B ψ (fun y => by rw [← Matrix.mulVec_mulVec, mulMat_mulVec, mulMat_mulVec, mul_assoc])).symm

def mulHom : B.A →* Matrix (Fin n) (Fin n) K.E where
  toFun := mulMat B ψ
  map_one' := mulMat_one B ψ
  map_mul' := mulMat_mul B ψ

theorem commutant (hs : B.P.Separable) (f : B.A →ₗ[K.E] B.A) (hf : ∀ y, f (B.g * y) = B.g * f y) (y : B.A) :
    f y = f 1 * y := by
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hs
  have key : f = LinearMap.mulRight K.E (f 1) := by
    refine b.ext fun i => ?_
    rw [hb i, LinearMap.mulRight_apply]
    generalize (i : ℕ) = k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', hf, ih, mul_assoc]
  rw [key, LinearMap.mulRight_apply, LinearMap.mulRight_apply, one_mul, mul_comm]

theorem stdH_mulVec_eq (M : Matrix (Fin n) (Fin n) K.E) (u v : Fin n → K.E) :
    stdH K n (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ ((Mᵀ * M.map K.c) *ᵥ fun k => K.c (v k)) := by
  have h1 : (fun k => K.c ((M *ᵥ v) k)) = M.map K.c *ᵥ fun k => K.c (v k) := by
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum]
  have h2 : stdH K n (M *ᵥ u) (M *ᵥ v) = (M *ᵥ u) ⬝ᵥ fun k => K.c ((M *ᵥ v) k) := rfl
  rw [h2, h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec]

theorem stdH_mulVec_iff (M : Matrix (Fin n) (Fin n) K.E) :
    (∀ u v, stdH K n (M *ᵥ u) (M *ᵥ v) = stdH K n u v) ↔ (M.map K.c)ᵀ * M = 1 := by
  constructor
  · intro h
    ext i j
    have := h (Pi.single j 1) (Pi.single i 1)
    simp [InertUnitOrb.stdH, Pi.single_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  · intro h u v
    have h' : Mᵀ * M.map K.c = 1 := by
      have := congrArg (fun X => X.map K.c) h
      simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero K.c) (map_one K.c)] at this
      convert this using 2
      ext a b; simp [K.c_c]
    rw [stdH_mulVec_eq, h', Matrix.one_mulVec]
    rfl

theorem isom_iff {γ' : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ} (hm : IsModel B γ' x ψ) (a : B.A) :
    (∀ u v, stdH K n (mulMat B ψ a *ᵥ u) (mulMat B ψ a *ᵥ v) = stdH K n u v) ↔ a * B.σ a = 1 := by
  have hh := hm.2.2
  constructor
  · intro h
    have h2 : ∀ y z, B.herm x (a * y) (a * z) = B.herm x y z := by
      intro y z
      rw [← hh, ← hh, ← mulMat_mulVec, ← mulMat_mulVec]
      exact h _ _
    have h3 : ∀ z, B.herm x (a * B.σ a - 1) z = 0 := by
      intro z
      have := h2 1 z
      simp only [InvAlg.herm] at this ⊢
      rw [show (x : B.A) * (a * B.σ a - 1) * B.σ z = (x : B.A) * (a * 1) * B.σ (a * z) - x * 1 * B.σ z by
        rw [map_mul]; ring, map_sub, this, sub_self]
    have h4 : ψ (a * B.σ a - 1) = 0 := by
      funext k
      have := h3 (ψ.symm (Pi.single k 1))
      rw [← hh, ψ.apply_symm_apply] at this
      simpa [InertUnitOrb.stdH, Pi.single_apply] using this
    exact sub_eq_zero.mp ((LinearEquiv.map_eq_zero_iff ψ).mp h4)
  · intro h u v
    obtain ⟨y, rfl⟩ := ψ.surjective u
    obtain ⟨z, rfl⟩ := ψ.surjective v
    rw [mulMat_mulVec, mulMat_mulVec, hh, hh]
    simp only [InvAlg.herm, map_mul]
    congr 1
    calc (x : B.A) * (a * y) * (B.σ a * B.σ z) = x * y * B.σ z * (a * B.σ a) := by ring
      _ = _ := by rw [h, mul_one]

theorem map_map_symm {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) R) :
    (M.map e).map e.symm = M := by
  ext i j; simp

theorem map_symm_map {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) S) :
    (M.map e.symm).map e = M := by
  ext i j; simp

theorem unitary_map {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}
    (e : K.E ≃+* w.adicCompletion E) (he : ∀ x, e (K.c x) = cj w (e x)) (M : Matrix (Fin n) (Fin n) K.E) :
    cT (cj w) (M.map e) * 1 * M.map e = 1 ↔ (M.map K.c)ᵀ * M = 1 := by
  have h1 : cT (cj w) (M.map e) = ((M.map K.c)ᵀ).map e := by
    ext i j; simp [cT, he]
  rw [h1, mul_one, ← Matrix.map_mul]
  constructor
  · intro h
    have : ((((M.map K.c)ᵀ * M).map e).map e.symm) = (1 : Matrix (Fin n) (Fin n) _).map e.symm := by rw [h]
    rw [map_map_symm] at this
    simpa using this
  · intro h
    rw [h]; simp

theorem cent_equiv_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := by
  intro E _ _ _ _ w hw K e he _ n B ψ x γ hm hs
  have hUL : UL n w = UJ (cj w) 1 := by simp [UL, hw]
  let ρ : B.A →* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (e.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) K.E →+* _).toMonoidHom.comp (mulHom B ψ)
  have hρa : ∀ a, ρ a = (mulMat B ψ a).map e := fun a => rfl
  have hγ' := eq_mulMat B ψ (fun y => (hm.2.1 y).symm)
  have hγ : (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = ρ B.g := by
    rw [hρa, ← hγ', map_symm_map]
  have hmem : ∀ u : B.Aˣ, u ∈ B.T → (Units.map ρ u : GLw n w) ∈ UL n w := by
    intro u hu
    rw [hUL]
    show cT (cj w) (((Units.map ρ u : GLw n w)) : Matrix (Fin n) (Fin n) _) * 1 * _ = 1
    rw [Units.coe_map, hρa, unitary_map e he, ← stdH_mulVec_iff, isom_iff B ψ hm]
    exact hu
  have hcent : ∀ (u : B.Aˣ) (hu : u ∈ B.T),
      (⟨Units.map ρ u, hmem u hu⟩ : UL n w) ∈ twCent (MonoidHom.id (UL n w)) γ := by
    intro u hu
    show _ * γ = γ * _
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, MonoidHom.id_apply, Units.coe_map, hγ]
    rw [← map_mul, ← map_mul, mul_comm]
  let φ : B.T →* twCent (MonoidHom.id (UL n w)) γ :=
    { toFun := fun u => ⟨⟨Units.map ρ u, hmem u u.2⟩, hcent u u.2⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp }
  have hφ : ∀ u : B.T, ((((φ u : twCent (MonoidHom.id (UL n w)) γ) : UL n w) : GLw n w) :
      Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (mulMat B ψ ((u : B.Aˣ) : B.A)).map e := fun u => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg (fun t : twCent (MonoidHom.id (UL n w)) γ =>
      (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) hab
    simp only [hφ, map_map_symm] at h1
    have h2 : ψ (((a : B.Aˣ) : B.A) * 1) = ψ (((b : B.Aˣ) : B.A) * 1) := by
      rw [← mulMat_mulVec, ← mulMat_mulVec, h1]
    apply Subtype.ext; apply Units.ext
    simpa using ψ.injective h2
  have hsurj : Function.Surjective φ := by
    intro t
    set T : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hT
    set T' := T.map e.symm with hT'
    have hc : T * (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) =
        (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) * T := by
      have := t.2
      change (t : UL n w) * γ = γ * (t : UL n w) at this
      have := congrArg (fun s : UL n w => ((s : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) this
      simpa using this
    have hc' : T' * mulMat B ψ B.g = mulMat B ψ B.g * T' := by
      rw [← hγ', hT', ← Matrix.map_mul, ← Matrix.map_mul, hc]
    let f : B.A →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' T' ∘ₗ ψ.toLinearMap
    have hfa : ∀ y, ψ (f y) = T' *ᵥ ψ y := by
      intro y; simp [f]
    have hf : ∀ y, f (B.g * y) = B.g * f y := by
      intro y
      apply ψ.injective
      rw [hfa, ← mulMat_mulVec, ← mulMat_mulVec, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc']
    have ha : ∀ y, T' *ᵥ ψ y = ψ (f 1 * y) := by
      intro y; rw [← hfa, commutant B hs f hf y]
    have hM := eq_mulMat B ψ ha
    have hTu : cT (cj w) T * 1 * T = 1 := by
      have hULmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := fun g hg => by rwa [hUL] at hg
      exact hULmem _ (t : UL n w).2
    have hu : f 1 * B.σ (f 1) = 1 := by
      rw [← isom_iff B ψ hm, stdH_mulVec_iff, ← hM, ← unitary_map e he, hT', map_symm_map]
      exact hTu
    let u : B.Aˣ := ⟨f 1, B.σ (f 1), hu, by rw [mul_comm]; exact hu⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    change (mulMat B ψ (f 1)).map e = T
    rw [← hM, hT', map_symm_map]
  refine ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun t y => ?_⟩
  have h1 : φ ((MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm t) = t :=
    (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).apply_symm_apply t
  conv_rhs => rw [← h1]
  rw [hφ, map_map_symm, mulMat_mulVec]

end GlobalTheory.CentTorusModel
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryCentralizer_equiv_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := by
  first | exact @GlobalTheory.CentTorusModel.cent_equiv_torus | exact GlobalTheory.CentTorusModel.cent_equiv_torus | (intros; apply GlobalTheory.CentTorusModel.cent_equiv_torus <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_matrix_iff_bounded_powers : ∀ (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) K.E), IsIntegral K.O M ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j, Valued.v (e ((M ^ k) i j)) ≤ WithZero.exp m := by
  first | exact @GlobalTheory.IntMatBound.isIntegral_iff_bounded | exact GlobalTheory.IntMatBound.isIntegral_iff_bounded | (intros; apply GlobalTheory.IntMatBound.isIntegral_iff_bounded <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb

theorem isIntegral_iff_of_mulVec {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (a : B.A)
    (M : Matrix (Fin n) (Fin n) K.E) (h : ∀ y, ψ (a * y) = M *ᵥ ψ y) : IsIntegral K.O a ↔ IsIntegral K.O M := by
  let b : Module.Basis (Fin n) K.E B.A := Module.Basis.ofEquivFun ψ
  let φ : B.A →ₐ[K.O] Matrix (Fin n) (Fin n) K.E := (Algebra.leftMulMatrix b).restrictScalars K.O
  have hinj : Function.Injective φ := Algebra.leftMulMatrix_injective b
  have hφ : φ a = M := by
    ext i j
    change Algebra.leftMulMatrix b a i j = M i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun, h]
    simp [b, Module.Basis.coe_ofEquivFun, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hφ]
  exact (isIntegral_algHom_iff φ hinj).symm

theorem cptPart_iff_intUnits_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := by
  intro E _ _ _ hE w hw K e he hint n B ψ x γ hmod hsep τ hτ t
  have hcont := (GlobalTheory.ConjAtPlace.main E hE w).1
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    unfold UL; rw [if_neg hw]
    have : ((UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Subgroup _) : Set (GLw n w)) =
        (fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
          (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ⁻¹' {1} := rfl
    rw [this]
    refine IsClosed.preimage ?_ isClosed_singleton
    unfold cT
    exact (((Units.continuous_val.matrix_map hcont).matrix_transpose).matrix_mul continuous_const).matrix_mul
      Units.continuous_val
  have hmat : ∀ (g : GLw n w) (k : ℕ) i j,
      e ((((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k) i j) =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    intro g k i j
    have : ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
      rw [Units.val_pow_eq_pow_val]
      exact (map_pow (e.symm.toRingHom.mapMatrix) _ k).symm
    rw [this, Matrix.map_apply, RingEquiv.apply_symm_apply]
  have key : ∀ s : twCent (MonoidHom.id (UL n w)) γ,
      IsCompact (closure (Subgroup.zpowers (s : UL n w) : Set (UL n w))) ↔ (τ s : B.Aˣ) ∈ intUnits K.O B.A := by
    intro s
    have hinv : ((τ s : B.Aˣ))⁻¹ = ((τ s⁻¹ : B.T) : B.Aˣ) := by rw [map_inv, Subgroup.coe_inv]
    have hI1 : IsIntegral K.O ((τ s : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w) ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B ψ _ _ (hτ s), GlobalTheory.T.isIntegral_matrix_iff_bounded_powers K e hint n]
      simp only [hmat]
    have hI2 : IsIntegral K.O ((((τ s : B.Aˣ))⁻¹ : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w)⁻¹ ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [hinv, isIntegral_iff_of_mulVec B ψ _ _ (hτ s⁻¹), GlobalTheory.T.isIntegral_matrix_iff_bounded_powers K e hint n]
      simp only [hmat, Subgroup.coe_inv]
    rw [GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries w n (UL n w) hcl (s : UL n w)]
    show _ ↔ IsIntegral K.O _ ∧ IsIntegral K.O _
    rw [hI1, hI2]
    simp only [SubgroupClass.coe_zpow]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨m, fun k i j => ?_⟩, ⟨m, fun k i j => ?_⟩⟩
      · have := hm (k : ℤ) i j
        rwa [zpow_natCast] at this
      · have := hm (-(k : ℤ)) i j
        rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨max m1 m2, fun k i j => ?_⟩
      rcases Int.eq_nat_or_neg k with ⟨l, rfl | rfl⟩
      · rw [zpow_natCast]
        exact (h1 l i j).trans (WithZero.exp_le_exp.2 (le_max_left _ _))
      · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
        exact (h2 l i j).trans (WithZero.exp_le_exp.2 (le_max_right _ _))
  let H' : Subgroup (UL n w) := ((intUnits K.O B.A).comap (B.T.subtype.comp τ.toMonoidHom)).map
    (twCent (MonoidHom.id (UL n w)) γ).subtype
  constructor
  · intro ht
    have hle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ H' := by
      rw [cptPart, Subgroup.closure_le]
      rintro u ⟨hu, hc⟩
      exact ⟨⟨u, hu⟩, (key ⟨u, hu⟩).1 hc, rfl⟩
    obtain ⟨t₀, ht₀, he₀⟩ := hle ht
    have : t₀ = t := Subtype.ext he₀
    subst this
    exact ht₀
  · intro ht
    exact Subgroup.subset_closure ⟨t.2, (key t).2 ht⟩

end GlobalTheory.InertUnitOrb
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactPart_centralizer_iff_integralUnits_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := by
  atlas_forward_decl GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.OrbIndUnit

theorem avg_const_fun {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (1 : H ⧸ (⊤ : Subgroup H))
  rw [finsum_unique]
  simp

theorem twOrb_id_indicator (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  unfold twOrb
  apply finsum_congr
  intro q
  set Q : G := Quotient.out q with hQ
  have hfun : (fun k : K => (K : Set G).indicator 1 ((Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k)))
      = fun _ => (K : Set G).indicator (1 : G → ℂ) (Q⁻¹ * γ * Q) := by
    funext k
    have he : (Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k) = (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k := by
      simp only [MonoidHom.id_apply]; group
    rw [he]
    by_cases h : Q⁻¹ * γ * Q ∈ K
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2
      simp [Set.indicator_apply, h, h']
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∉ K := by
        intro h'
        apply h
        have := K.mul_mem (K.mul_mem k.2 h') (K.inv_mem k.2)
        simpa [mul_assoc] using this
      simp [Set.indicator_apply, h, h']
  rw [hfun, avg_const_fun]
  by_cases h : Q⁻¹ * γ * Q ∈ K
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

end GlobalTheory.OrbIndUnit
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_indicator_eq_finsum_relIndex : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.OrbIndUnit.twOrb_id_indicator | exact GlobalTheory.OrbIndUnit.twOrb_id_indicator | (intros; apply GlobalTheory.OrbIndUnit.twOrb_id_indicator <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory

theorem relIndex_eq_of_mulEquiv_subgroup : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := by
  intro G H _ _ T S τ A₁ A₂ B₁ B₂ h₁ h₂ e₁ e₂
  have key : ∀ (A : Subgroup G) (B : Subgroup H), (∀ t : T, (t : G) ∈ A ↔ ((τ t : S) : H) ∈ B) →
      (A.subgroupOf T).map τ.toMonoidHom = (B ⊓ S).subgroupOf S := by
    intro A B e
    ext s
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, e]
    simp
  rw [← Subgroup.relIndex_subgroupOf h₂, ← Subgroup.relIndex_subgroupOf (inf_le_right : B₂ ⊓ S ≤ S),
    ← key A₁ B₁ e₁, ← key A₂ B₂ e₂,
    Subgroup.relIndex_map_map_of_injective _ _ τ.injective]

end GlobalTheory
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_eq_relIndex_inf_of_mulEquiv_subgroup : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := by
  first | exact @GlobalTheory.relIndex_eq_of_mulEquiv_subgroup | exact GlobalTheory.relIndex_eq_of_mulEquiv_subgroup | (intros; apply GlobalTheory.relIndex_eq_of_mulEquiv_subgroup <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma
theorem unitLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := GlobalTheory.T.unitaryLattice_isLattice_selfDual_hermitianModel
theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := GlobalTheory.T.unitLattice_stable_iff_conj_integral
theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := GlobalTheory.T.unitaryLattice_eq_iff_inv_mul_integral
theorem exists_unitLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := GlobalTheory.T.self_dual_lattice_standard_hermitian
theorem exists_torus_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := GlobalTheory.T.localUnitaryCentralizer_equiv_normOneTorus
theorem cptPart_iff_intUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := GlobalTheory.T.compactPart_centralizer_iff_integralUnits_of_model
theorem twOrb_unit : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := GlobalTheory.T.orbitalIntegral_indicator_eq_finsum_relIndex
theorem relIndex_transport : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := GlobalTheory.T.relIndex_eq_relIndex_inf_of_mulEquiv_subgroup
end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) (a : Aˣ) (y : A) :
    y ∈ mulLat O (a : A) L ↔ ((a⁻¹ : Aˣ) : A) * y ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [← mul_assoc] using hz
  · intro h
    exact ⟨((a⁻¹ : Aˣ) : A) * y, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff : ∀ (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (L : Submodule O A) (u : Aˣ), u ∈ stabLat O L ↔ mulLat O (u : A) L = L := by
  intro O _ A _ _ L u
  constructor
  · intro h
    have h' : ∀ y, y ∈ L ↔ (u : A) * y ∈ L := h
    ext y
    rw [mem_mulLat_unit, h', ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    have hy := mem_mulLat_unit L u ((u : A) * y)
    rw [h, ← mul_assoc, Units.inv_mul, one_mul] at hy
    exact hy.symm

theorem unitLat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (t q : UL n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → unitLat e B ψ (t * q) = mulLat K.O (a : B.A) (unitLat e B ψ q) := by
  intro E _ _ _ hE w hw K e he hint n B ψ t q a ha
  have hmap : ∀ (g h : UL n w), ((((g * h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) =
      (((g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm *
        (((h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
    intro g h
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hinv : ∀ y, ((((t⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y =
      ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
    intro y
    have h1 : ψ y = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ
        ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
      rw [← ha, ← mul_assoc, Units.mul_inv, one_mul]
    rw [h1, Matrix.mulVec_mulVec, ← hmap, inv_mul_cancel]
    simp
  have key : ∀ (r : UL n w) (z : B.A), z ∈ unitLat e B ψ r ↔
      ∀ i, (((((r⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ z) i ∈
        (algebraMap K.O K.E).range := fun r z => Iff.rfl
  ext y
  rw [key, _root_.mul_inv_rev, hmap, ← Matrix.mulVec_mulVec, hinv, ← key, mem_mulLat_unit]

end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mulLat_one' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) :
    mulLat O (1 : A) L = L := by
  simp [mulLat]

theorem mulLat_mul' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a b : A) (L : Submodule O A) :
    mulLat O (a * b) L = mulLat O a (mulLat O b L) := by
  rw [mulLat, mulLat, mulLat, LinearMap.mulLeft_mul, Submodule.map_comp]

theorem orbRel_equivalence {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (G : Subgroup Aˣ)
    (X : Set (Submodule O A)) :
    Equivalence (fun L M : X => ∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)) where
  refl L := ⟨1, G.one_mem, by simp [mulLat_one']⟩
  symm := by
    rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, G.inv_mem ht, ?_⟩
    rw [h, ← mulLat_mul', Units.inv_mul, mulLat_one']
  trans := by
    rintro L M N ⟨t, ht, h⟩ ⟨s, hs, h'⟩
    refine ⟨s * t, G.mul_mem hs ht, ?_⟩
    rw [h', h, Units.val_mul, mulLat_mul']

theorem ratCast_finsum' {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, ((f i : ℚ) : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact AddMonoidHom.map_finsum (Rat.castHom ℂ).toAddMonoidHom h
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support]
    · simp
    · have : Function.support (fun i => ((f i : ℚ) : ℂ)) = Function.support f := by
        ext i; simp
      rwa [this]

theorem finsum_ite_subtype' {α M : Type} [AddCommMonoid M] (p : α → Prop) [DecidablePred p] (f : α → M) :
    ∑ᶠ i, (if p i then f i else 0) = ∑ᶠ i : Subtype p, f i := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun i => finsum_eq_if.symm

theorem orb_eq_N : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (γ : UL n w) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B (γ.1.val.map e.symm) x ψ → twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e he hint n B hsep γ x ψ hM
  obtain ⟨hx, hg, hh⟩ := hM
  obtain ⟨τ, hτ⟩ := exists_torus_equiv E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep
  have hcpt := cptPart_iff_intUnits E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep τ hτ
  have hS1 := unitLat_selfDual E hE w hw K e he hint n B ψ x hx hh
  have hS1b := unitLat_stable_iff E hE w hw K e he hint n B ψ γ hg
  have hS2 := unitLat_eq_iff E hE w hw K e he hint n B ψ
  have hS3 := exists_unitLat_eq E hE w hw K e he hint n B ψ x hx hh
  have hS6 : ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (q : UL n w),
      unitLat e B ψ ((t : UL n w) * q) = mulLat K.O ((τ t : B.Aˣ) : B.A) (unitLat e B ψ q) :=
    fun t q => unitLat_mul E hE w hw K e he hint n B ψ t q (τ t) (hτ t)
  have hcomm : ∀ s t : twCent (MonoidHom.id (UL n w)) γ, (s : UL n w) * t = t * s := by
    intro s t
    have h1 : τ (s * t) = τ (t * s) := by rw [map_mul, map_mul, mul_comm]
    have := congrArg Subtype.val (τ.injective h1)
    simpa using this
  have hX : ∀ q : UL n w, q⁻¹ * γ * q ∈ KL n w → unitLat e B ψ q ∈ B.X x := fun q hq =>
    ⟨(hS1 q).1, (hS1b q).2 hq, (hS1 q).2⟩
  have hrel : ∀ L M : B.X x, (Quot.mk _ L : Orb K.O B.T (B.X x)) = Quot.mk _ M →
      ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) L := fun L M h =>
    (orbRel_equivalence B.T (B.X x)).eqvGen_iff.mp (Quot.eqvGen_exact h)
  have hcle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ twCent (MonoidHom.id (UL n w)) γ :=
    (Subgroup.closure_le _).mpr fun s hs => hs.1
  have hconj : ∀ (Q s : UL n w), s ∈ (KL n w).map (MulAut.conj Q).toMonoidHom ↔ Q⁻¹ * s * Q ∈ KL n w := by
    intro Q s
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [twOrb_unit]
  unfold InvAlg.N orbSum
  rw [ratCast_finsum']
  rw [finsum_ite_subtype']
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) γ : Set (UL n w)) (KL n w : Set (UL n w)) //
      (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ KL n w} → Orb K.O B.T (B.X x) :=
    fun q => Quot.mk _ ⟨unitLat e B ψ (Quotient.out q.1), hX _ q.2⟩
  refine finsum_eq_of_bijective φ ⟨?_, ?_⟩ ?_
  · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    obtain ⟨a, ha, hQ⟩ := hrel _ _ h
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6, hS2] at hQ
    apply Subtype.ext
    show q = q'
    rw [← DoubleCoset.out_eq' _ _ q, ← DoubleCoset.out_eq' _ _ q', DoubleCoset.eq]
    exact ⟨t, t.2, _, (KL n w).inv_mem hQ, by group⟩
  · intro o
    set R := Quot.out o
    obtain ⟨q0, hq0⟩ := hS3 R.1 R.2.1 R.2.2.2
    have hq0K : q0⁻¹ * γ * q0 ∈ KL n w := (hS1b q0).1 (hq0 ▸ R.2.2.1)
    obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0
    have hhγ : h * γ = γ * h := hh
    have hP : (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0))⁻¹ * γ *
        Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0) ∈ KL n w := by
      rw [hout]
      have : (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * (q0⁻¹ * γ * q0) * k := by
        calc (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * q0⁻¹ * (h⁻¹ * (γ * h)) * q0 * k := by group
          _ = k⁻¹ * (q0⁻¹ * γ * q0) * k := by rw [← hhγ]; group
      rw [this]
      exact (KL n w).mul_mem ((KL n w).mul_mem ((KL n w).inv_mem hk) hq0K) hk
    refine ⟨⟨_, hP⟩, ?_⟩
    show Quot.mk _ _ = o
    rw [← Quot.out_eq o]
    refine (Quot.sound ?_).symm
    refine ⟨τ ⟨h, hh⟩, (τ ⟨h, hh⟩).2, ?_⟩
    show unitLat e B ψ _ = mulLat K.O _ R.1
    rw [hout, ← hq0, ← hS6]
    exact ((hS2 _ _).2 (by simpa [mul_assoc] using hk)).symm
  · rintro ⟨q, hq⟩
    set R := Quot.out (φ ⟨q, hq⟩)
    have hR : (Quot.mk _ R : Orb K.O B.T (B.X x)) = φ ⟨q, hq⟩ := Quot.out_eq _
    obtain ⟨a, ha, hRa⟩ := hrel _ _ hR.symm
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6] at hRa
    simp only [one_mul, Rat.cast_natCast]
    congr 1
    refine relIndex_transport (UL n w) B.Aˣ _ B.T τ _ _ (stabLat K.O R.1) (intUnits K.O B.A) inf_le_left hcle ?_ hcpt
    intro s
    rw [mem_stabLat_iff, hRa, ← hS6, hS2, Subgroup.mem_inf, hconj]
    simp only [SetLike.coe_mem, true_and]
    have : ((s : UL n w) * ((t : UL n w) * Quotient.out q))⁻¹ * ((t : UL n w) * Quotient.out q) =
        ((Quotient.out q)⁻¹ * s * Quotient.out q)⁻¹ := by
      rw [← mul_assoc (s : UL n w), hcomm s t]
      group
    rw [this]
    exact inv_mem_iff.symm

end GlobalTheory.InertUnitOrb
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_orbitalIntegral_unit_eq_lattice_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (γ : UL n w) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B (γ.1.val.map e.symm) x ψ → twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  first | exact @GlobalTheory.InertUnitOrb.orb_eq_N | exact GlobalTheory.InertUnitOrb.orb_eq_N | (intros; apply GlobalTheory.InertUnitOrb.orb_eq_N <;> assumption)
end
