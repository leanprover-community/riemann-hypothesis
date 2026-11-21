import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.StCoiLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsExist
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem charpoly_single {F : Type} [CommRing F] {m : ℕ} (i : Fin (m + 1)) :
    (single i i (1 : F)).charpoly = X ^ (m + 1) - X ^ m := by
  rw [← Matrix.diagonal_single, Matrix.charpoly_diagonal, Fin.prod_univ_succAbove _ i]
  simp [Pi.single_apply, Fin.succAbove_ne]
  ring

theorem UpperTheory.V.Pa.idem_nil :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} (D : Det n B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), D.IsCH → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r y = 0 → ∃ M : ℕ, y ^ M ∈ maximalIdeal B • (⊤ : Submodule B E)) ∧ ∀ (e : E) (i : Fin n), IsIdempotentElem e → r e = single i i 1 → D.D B[X] (1 + X ⊗ₜ e) = 1 + X := by
  intro B E F _ _ _ _ _ _ n D r hch hker hchi
  refine ⟨fun y hy => ⟨n, ?_⟩, fun e i he hre => ?_⟩
  · have h0 := ((d_chS D B).2.2 hch).2 y
    have h1 : (X ^ n - D.chi y).map (algebraMap B F) = 0 := by
      rw [Polynomial.map_sub, hchi, hy, Matrix.charpoly_zero]; simp
    have h2 : y ^ n = aeval y (X ^ n - D.chi y) := by simp [h0]
    rw [h2, aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← hker, RingHom.mem_ker, ← coeff_map, h1, coeff_zero]
  · obtain ⟨k, -, hk⟩ := d_idem_rank D e he
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    have hc := hchi e
    rw [hre, charpoly_single] at hc
    have hl : ∀ j, algebraMap B F (D.lam j e) = (-1) ^ j * (X ^ (m + 1) - X ^ m : F[X]).coeff (m + 1 - j) := by
      intro j
      rw [← hc, coeff_map, Det.lam]; simp
    have h3 : (D.D B[X] (1 + X ⊗ₜ e)).map (algebraMap B F) = 1 + X := by
      rw [(d_chi D e).2.2.1, Polynomial.map_sum, Finset.sum_range_succ', Finset.sum_range_succ',
        Finset.sum_eq_zero]
      · simp [hl, coeff_X_pow, add_comm]
      · intro j hj
        rw [Finset.mem_range] at hj
        have a1 : ¬ (m - (j + 1) = m + 1) := by omega
        have a2 : ¬ (m - (j + 1) = m) := by omega
        simp [hl, coeff_X_pow, a1, a2]
    rw [hk] at h3 ⊢
    have h4 := congrArg natDegree h3
    have h5 : natDegree (1 + X : F[X]) = 1 := by rw [add_comm]; exact natDegree_X_add_C 1
    have h6 : Monic (1 + X : F[X]) := by rw [add_comm]; exact monic_X_add_C 1
    rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, h6.natDegree_pow, h5, mul_one] at h4
    rw [h4, pow_one]
end

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem oB_lt {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) :
    ((oB n a i : Fin n) : ℕ) < a ↔ (i : ℕ) < a := by
  unfold oB
  split_ifs with hi
  · simp only [hi, iff_true]
    exact h1
  · simp only [hi, iff_false, not_lt]
    have := i.2
    omega

private theorem oB_oB {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) : oB n a (oB n a i) = oB n a i := by
  have key := oB_lt h1 h2 i
  unfold oB at key ⊢
  by_cases hi : (i : ℕ) < a
  · have : ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a := key.2 hi
    simp only [hi, if_true] at this ⊢
    simp only [this, if_true]
  · have : ¬ ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a :=
      fun h => hi (key.1 h)
    simp only [hi, if_false] at this ⊢
    simp only [this, if_false]

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (p q : Fin n) (h : (p : ℕ) < a ↔ (q : ℕ) < a) :
    (single p q 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Matrix.single_apply]
  split_ifs with hpq
  · obtain ⟨rfl, rfl⟩ := hpq
    exact absurd h hij
  · exact Submodule.zero_mem _

theorem UpperTheory.V.Pa.idem :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Module.Finite B E] (a : ℕ) (D : Det n B E) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), 1 ≤ a → a ≤ n → IsUnit (2 : B) → D.IsCH → (∀ y, T.tr y = D.tr y) → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ Z ∈ Ev F F n a, ∃ y, r y = Z) → ∃ U : T.Units (Fin n) (oB n a), (∀ i, r (U.x i) = single (oB n a i) i 1) ∧ ∀ i, D.D B[X] (1 + X ⊗ₜ U.ep i) = 1 + X := by
  intro B E F _ _ _ _ _ _ n _ _ _ a D T r h1 h2 h2u hCH htr hker hchi hst hsurj
  have hn : 1 ≤ n := le_trans h1 h2
  haveI : IsAdicComplete (maximalIdeal B) E := GlobalTheory.isAdicComplete_of_finite (maximalIdeal B) E
  obtain ⟨hnil, hidem⟩ := idem_nil D r hCH hker hchi
  have hdiag : ∀ i : Fin n, ∃ y, r y = single i i 1 := fun i =>
    hsurj _ (single_mem i i Iff.rfl)
  obtain ⟨ep, hcoi, hstep, hrep⟩ :=
    st_coi_lift T (maximalIdeal B) r h2u (le_of_eq hker.symm) hnil hst hdiag
  have hD : ∀ i, D.D B[X] (1 + X ⊗ₜ ep i) = 1 + X := fun i =>
    hidem (ep i) i (hcoi.idem i) (hrep i)
  have hcorner := fun i => d_corner D (ep i) hCH (hcoi.idem i) (hD i) hn
  haveI : HenselianRing B (RingHom.ker (algebraMap B F)) := by
    rw [hker]
    infer_instance
  obtain ⟨U, hUep, hUx⟩ := units_exist T (oB n a) r ep h2u (fun i => oB_oB h1 h2 i) hst
    (fun i => hsurj _ (single_mem _ _ (oB_lt h1 h2 i))) hcoi hstep hrep
    (fun i => by rw [htr]; exact (hcorner i).2.1)
    (fun i y => ⟨D.tr (ep i * y), (hcorner i).1 y⟩)
  refine ⟨U, hUx, fun i => ?_⟩
  rw [hUep]
  exact hD i
end
