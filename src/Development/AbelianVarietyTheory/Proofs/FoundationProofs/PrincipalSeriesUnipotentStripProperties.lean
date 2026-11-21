import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import BuildAid.ForwardExisting

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem minor_of_triangular (g : GL (Fin n) k) (m : Fin n)
    (h : (∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) :
    minor g m = ∏ i ∈ Finset.univ.filter (fun i => i ≤ m), g.val i i := by
  unfold minor
  have hdet : (g.val.toSquareBlockProp fun i => i ≤ m).det = ∏ i : {i : Fin n // i ≤ m}, g.val i i := by
    rcases h with h | h
    · rw [Matrix.det_of_lowerTriangular]
      · rfl
      · intro i j hij
        exact h i j (OrderDual.toDual_lt_toDual.1 hij)
    · rw [Matrix.det_of_upperTriangular]
      · rfl
      · intro i j hij
        exact h i j hij
  rw [hdet]
  exact (Finset.prod_subtype (Finset.univ.filter (fun i => i ≤ m)) (p := fun i => i ≤ m)
    (fun x => by simp) (fun i => g.val i i)).symm

theorem prod_div_nxt (ψ : Fin n → kˣ →* ℂˣ) (a : Fin n) (u : kˣ) :
    ∏ m ∈ Finset.univ.filter (fun m => a ≤ m), (ψ m / nxt ψ m) u = ψ a u := by
  let f : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hf : ∀ m : Fin n, f m = ψ m u := fun m => by
    show (if h : (m : ℕ) < n then ψ ⟨m, h⟩ u else 1) = ψ m u
    rw [dif_pos m.isLt]
  have hnx : ∀ m : Fin n, nxt ψ m u = f (m + 1) := by
    intro m
    unfold nxt
    split_ifs with h
    · simp [f, h]
    · simp [f, h]
  let G : ℕ → ℂˣ := fun j => if (a : ℕ) ≤ j then (f (j + 1))⁻¹ / (f j)⁻¹ else 1
  rw [Finset.prod_filter]
  have hterm : ∀ m : Fin n, (if a ≤ m then (ψ m / nxt ψ m) u else 1) = G m := by
    intro m
    simp only [G, Fin.le_def, MonoidHom.div_apply, hnx, ← hf m, inv_div_inv]
  rw [Finset.prod_congr rfl fun m _ => hterm m, Fin.prod_univ_eq_prod_range G n, ← Finset.prod_filter]
  have hs : (Finset.range n).filter (fun j => (a : ℕ) ≤ j) = Finset.Ico (a : ℕ) n := by
    ext j; simp; omega
  rw [hs, Finset.prod_Ico_div (f := fun j => (f j)⁻¹) a.isLt.le]
  simp [f, hf a]

theorem theta_of_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  intro k _ _ _ _ n ψ g t ht hd htri
  have hmin : ∀ m, minor g m = ((∏ i ∈ Finset.univ.filter (fun i => i ≤ m), t i : kˣ) : k) := by
    intro m
    rw [minor_of_triangular g m htri, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hd i
  have hev : ∀ (χ : kˣ →* ℂˣ) (u : kˣ), valuation k (u : k) = 1 → ev χ u = χ u := by
    intro χ u hu
    unfold ev
    rw [dif_pos hu]
    congr 2
    ext
    rfl
  have hval : ∀ s : Finset (Fin n), valuation k ((∏ i ∈ s, t i : kˣ) : k) = 1 := by
    intro s
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_eq_one fun i _ => ht i
  unfold theta
  rw [Finset.prod_congr rfl fun m _ => by rw [hmin m, hev _ _ (hval _)]]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp only [map_prod]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter (fun m => i ≤ m))
    (by intro x y; simp)]
  exact Finset.prod_congr rfl fun i _ => prod_div_nxt ψ i (t i)

end GlobalTheory.PsType
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_of_triangular | exact GlobalTheory.PsType.theta_of_triangular | (intros; apply GlobalTheory.PsType.theta_of_triangular <;> assumption)
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_int_det {I : Type} [Fintype I] [DecidableEq I] {g : GL I k}
    (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) : g ∈ KO k I := by
  classical
  let M : Matrix I I 𝒪[k] := fun i j => ⟨g.val i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  have hmap : M.map (algebraMap 𝒪[k] k) = g.val := by
    ext i j
    rfl
  have hdet : IsUnit M.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_of_one' ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hd]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  refine ⟨u, ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, hu]
  rfl

end GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem strip_off {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : y.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_neg h] at h0
  exact h0

theorem strip_on {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) :
    valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j) := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_pos h] at h0
  exact h0

theorem strip_lower {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : j < i) : y.val i j = 0 := by
  have hji : (j : ℕ) < (i : ℕ) := h
  rw [strip_off hy i j (fun hc => by omega), Matrix.one_apply_ne (ne_of_gt h)]

theorem strip_diag {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i : Fin n) : y.val i i = 1 := by
  rw [strip_off hy i i (fun hc => by omega), Matrix.one_apply_eq]

theorem strip_det {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m) :
    y.val.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => strip_lower hy i j h)]
  simp [strip_diag hy]

theorem strip_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ n ψ r ϖ hϖ hϖ1 hunif hcut
  have hent : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → ∀ i j : Fin n,
      ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → valuation k (y.val i j) ≤ 1 := by
    intro m y hy i j h
    rw [strip_off hy i j h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have hdet1 : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → valuation k y.val.det = 1 := by
    intro m y hy
    rw [strip_det hy, map_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    refine (show y ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (y.val i j) from ⟨?_, ?_⟩)
    · refine mem_KO_of_int_det (fun i j => ?_) (hdet1 0 y hy)
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).1
        rwa [pow_zero, one_mul] at h0
      · exact hent 0 y hy i j h
    · intro i j hij
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).2
        rwa [pow_zero, one_mul] at h0
      · rw [strip_off hy i j h, Matrix.one_apply_ne (ne_of_lt hij)]
        exact triv_zero _
  · intro m y hy
    rw [GlobalTheory.T.principalSeriesTypeCharacter_triangular k n ψ y (fun _ => 1) (fun _ => by simp) (fun i => by simp [strip_diag hy i])
      (Or.inr fun i j h => strip_lower hy i j h)]
    simp
  · intro y hy
    refine mem_KO_of_int_det (fun i j => ?_) (hdet1 1 y hy)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · obtain ⟨h1, h2⟩ := strip_on hy i j h
      rw [pow_one] at h1 h2
      have hlt : valuation k (ϖ * y.val i j) < 1 := by
        refine lt_of_le_of_ne h1 fun heq => hcut i j h.1 h.2 ?_
        exact triv_mono _ _ _ (le_of_eq (by rw [heq, map_one])) h2
      have hle := hunif _ hlt
      rw [map_mul] at hle
      have hpos : 0 < valuation k ϖ := zero_lt_iff.2 ((map_ne_zero _).2 hϖ)
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    · exact hent 1 y hy i j h
  · intro z hz m y
    set d : Fin n → k := fun i : Fin n => if (i : ℕ) < r then ϖ else 1 with hd_def
    have hd : ∀ i, d i ≠ 0 := by
      intro i
      simp only [hd_def]
      split_ifs
      exacts [hϖ, one_ne_zero]
    have hzz : z.val * (z⁻¹).val = 1 := by simp
    have hzinv : (z⁻¹).val = Matrix.diagonal (fun i => (d i)⁻¹) := by
      calc (z⁻¹).val = (Matrix.diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by
            rw [hz, Matrix.diagonal_mul_diagonal]
            rw [show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : k) from funext fun i => inv_mul_cancel₀ (hd i)]
            rw [Matrix.diagonal_one, one_mul]
        _ = Matrix.diagonal (fun i => (d i)⁻¹) := by rw [mul_assoc, hzz, mul_one]
    have hentry : ∀ i j : Fin n, (z * y * z⁻¹).val i j = d i * y.val i j * (d j)⁻¹ := by
      intro i j
      rw [Units.val_mul, Units.val_mul, hz, hzinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [strip, Set.mem_ofPred_eq, hentry]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [if_pos h, if_pos h]
      have hdi : d i = ϖ := by simp only [hd_def]; rw [if_pos h.1]
      have hdj : d j = 1 := by simp only [hd_def]; rw [if_neg (by omega)]
      rw [hdi, hdj, show ϖ ^ m * (ϖ * y.val i j * (1 : k)⁻¹) = ϖ ^ (m + 1) * y.val i j by ring]
    · rw [if_neg h, if_neg h]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, mul_comm (d i), mul_inv_cancel_right₀ (hd i)]
      · rw [Matrix.one_apply_ne hij]
        simp [hd i, hd j]

end GlobalTheory.PsType
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesUnipotentStrip_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  atlas_forward_decl GlobalTheory.PsType.strip_props
end
