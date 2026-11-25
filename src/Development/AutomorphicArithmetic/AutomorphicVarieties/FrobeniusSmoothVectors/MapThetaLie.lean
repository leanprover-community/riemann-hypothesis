module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Mathlib.Tactic.Linter.Style
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C]
  {K : Ideal C} (u : K →ₗ[O] ResidueField O)

private theorem evk_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, f i ∈ K) :
    evK K u (∑ i ∈ s, f i) = ∑ i ∈ s, evK K u (f i) := by
  have hsum : (⟨∑ i ∈ s, f i, K.sum_mem fun i _ => hf i⟩ : K) = ∑ i ∈ s, ⟨f i, hf i⟩ :=
    Subtype.ext (Submodule.coe_sum K (fun i => ⟨f i, hf i⟩) s).symm
  rw [evK_of_mem u (K.sum_mem fun i _ => hf i), hsum, map_sum]
  exact Finset.sum_congr rfl fun i _ => (evK_of_mem u (hf i)).symm

private theorem evk_mul [IsCO O C] (hK : maximalIdeal C * K = ⊥) (a : C) {x : C} (hx : x ∈ K) :
    evK K u (a * x) = res O C a * evK K u x := by
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
  have h0 : (a - algebraMap O C b) * x = 0 := by
    have := Ideal.mul_mem_mul hb hx
    rwa [hK, Ideal.mem_bot] at this
  have h1 : res O C a = algebraMap O _ b := by
    have := (res_eq_zero_iff O C _).2 hb
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [evK_of_mem u hx, evK_of_mem u (K.mul_mem_left a hx), h1, ← Algebra.smul_def, ← map_smul]
  congr 1
  apply Subtype.ext
  show a * x = b • x
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, h0]

variable {n : ℕ}

private theorem mem_left {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (A * Z) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_left _ (hZ k j)

private theorem mem_right {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (Z * A) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_right _ (hZ i k)

private theorem map_left [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_left _ (hZ k j)]
  exact Finset.sum_congr rfl fun k _ => evk_mul u hK _ (hZ k j)

private theorem map_right [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_right _ (hZ i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, evk_mul u hK _ (hZ i k), mul_comm]
  rfl

private theorem mem_theta {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K) (i j : Fin n) :
    thetaLie Z i j ∈ K :=
  K.neg_mem (mem_right (mem_left (Z := Zᵀ) (fun i j => hZ j i) _) _ i j)

private theorem map_thetaLie [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) : (thetaLie Z).map (evK K u) = thetaLie (Z.map (evK K u)) := by
  have hT : ∀ i j, Zᵀ i j ∈ K := fun i j => hZ j i
  have hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have e : (Jmat C n * Zᵀ * Jmat C n).map (evK K u) =
      Jmat (ResidueField O) n * (Z.map (evK K u))ᵀ * Jmat (ResidueField O) n := by
    rw [map_right u hK (mem_left hT _), map_left u hK hT, hJ]
    rfl
  unfold thetaLie
  rw [← e]
  ext i j
  have h := mem_right (mem_left hT (Jmat C n)) (Jmat C n) i j
  simp only [Matrix.map_apply, Matrix.neg_apply, evK_of_mem u (K.neg_mem h), evK_of_mem u h]
  exact map_neg u ⟨_, h⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_evk :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (K : Ideal C) (u : K →ₗ[O] ResidueField O), maximalIdeal C * K = ⊥ → K ≤ maximalIdeal C → ∀ Z : Matrix (Fin n) (Fin n) C, (∀ i j, Z i j ∈ K) → (∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 ∧ (Z + Z').map (evK K u) = Z.map (evK K u) + Z'.map (evK K u) ∧ (Z - Z').map (evK K u) = Z.map (evK K u) - Z'.map (evK K u)) ∧ (∀ A : Matrix (Fin n) (Fin n) C, (∀ i j, (A * Z) i j ∈ K ∧ (Z * A) i j ∈ K) ∧ (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) ∧ (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C)) ∧ ∀ x : GG (m := n) (R := C), (∀ i j, x.adFun Z i j ∈ K) ∧ (x.adFun Z).map (evK K u) = (GG.map (res O C : C →+* ResidueField O) x).adFun (Z.map (evK K u)) ∧ ∀ z : GL (Fin n) C, (z : Matrix (Fin n) (Fin n) C) = 1 + Z → (x * GG.ofGL z * x⁻¹).mat = 1 + x.adFun Z := by
  intro O _ _ C _ _ _ n K u hK hKm Z hZ
  have hsq : ∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 := fun Z' hZ' => by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := Ideal.mul_mem_mul (hKm (hZ i k)) (hZ' k j)
    rwa [hK, Ideal.mem_bot] at this
  refine ⟨fun Z' hZ' => ⟨hsq Z' hZ', ?_, ?_⟩,
    fun A => ⟨fun i j => ⟨mem_left hZ A i j, mem_right hZ A i j⟩, map_left u hK hZ A, map_right u hK hZ A⟩,
    fun x => ?_⟩
  · ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, evK_of_mem u (K.add_mem (hZ i j) (hZ' i j)),
      evK_of_mem u (hZ i j), evK_of_mem u (hZ' i j)]
    exact map_add u ⟨_, hZ i j⟩ ⟨_, hZ' i j⟩
  · ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, evK_of_mem u (K.sub_mem (hZ i j) (hZ' i j)),
      evK_of_mem u (hZ i j), evK_of_mem u (hZ' i j)]
    exact map_sub u ⟨_, hZ i j⟩ ⟨_, hZ' i j⟩
  have hY : ∀ i j, (if x.right = 1 then Z else thetaLie Z) i j ∈ K := fun i j => by
    split_ifs
    · exact hZ i j
    · exact mem_theta hZ i j
  refine ⟨mem_right (mem_left hY _) _, ?_, fun z hz => ?_⟩
  · have hY' : (if x.right = 1 then Z else thetaLie Z).map (evK K u) =
        if x.right = 1 then Z.map (evK K u) else thetaLie (Z.map (evK K u)) := by
      split_ifs
      · rfl
      · exact map_thetaLie u hK hZ
    unfold GG.adFun
    rw [map_right u hK (mem_left hY _), map_left u hK hY, hY']
    rfl
  · have hinv : ((z⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = 1 - Z := by
      have : (z : Matrix (Fin n) (Fin n) C) * (1 - Z) = 1 := by
        rw [hz, add_mul, mul_sub, mul_sub, hsq Z hZ]
        simp
      exact Units.inv_eq_of_mul_eq_one_right this
    have hl : (x * GG.ofGL z * x⁻¹).left = x.left * sgnAct n C x.right z * x.left⁻¹ := by
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one,
        ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hs : ((sgnAct n C x.right z : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
        1 + (if x.right = 1 then Z else thetaLie Z) := by
      rcases Int.units_eq_one_or x.right with h | h
      · rw [h, sgnAct_one, ite_eq_left rfl, hz]
      · rw [h, sgnAct_neg_one, ite_eq_right (by decide), theta_val, hinv, thetaLie, Matrix.transpose_sub,
          Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat,
          sub_eq_add_neg]
    unfold GG.adFun GG.mat
    rw [hl, Units.val_mul, Units.val_mul, hs, mul_add, add_mul, mul_one, Units.mul_inv]
