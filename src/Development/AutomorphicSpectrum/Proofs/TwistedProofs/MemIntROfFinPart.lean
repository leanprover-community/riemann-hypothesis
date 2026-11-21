import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCX
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean

section
open Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Twist.FullRank

theorem norm_det_le_factorial_mul_prod {a : ℕ} (P : Matrix (Fin a) (Fin a) ℂ) (c : Fin a → ℝ)
    (hc : ∀ r s, ‖P r s‖ ≤ c r) : ‖P.det‖ ≤ a.factorial * ∏ r, c r := by
  rw [det_apply]
  calc ‖∑ σ : Equiv.Perm (Fin a), Equiv.Perm.sign σ • ∏ i, P (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin a), ‖Equiv.Perm.sign σ • ∏ i, P (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin a), ∏ r, c r := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have h1 : ‖Equiv.Perm.sign σ • ∏ i, P (σ i) i‖ = ∏ i, ‖P (σ i) i‖ := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, norm_prod]
        rw [h1, ← Equiv.prod_comp σ c]
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hc _ _
    _ = a.factorial * ∏ r, c r := by
        simp [Finset.card_univ, Fintype.card_perm]

theorem exists_exchange {E : Type} [Field E] {a d : ℕ} (γ : Matrix (Fin d) (Fin a) E)
    (hγ : γ.rank = a) (v : Fin a → E) (hv : v ≠ 0) :
    ∃ (s : Fin a → Fin d) (k : Fin a), ((γ.submatrix s id).updateRow k v).det ≠ 0 := by
  classical
  have hfr : Module.finrank E (Submodule.span E (Set.range γ.row)) = a := by
    rw [← Matrix.rank_eq_finrank_span_row, hγ]
  obtain ⟨f, hf, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq E (Set.range γ.row)
  have hs : ∀ i : Fin a, ∃ r, γ.row r = f (Fin.cast hfr.symm i) := fun i => hf _
  choose s hs using hs
  have hli' : LinearIndependent E (γ.submatrix s id).row := by
    have h2 := hli.comp (Fin.cast hfr.symm) (Fin.cast_injective _)
    have h3 : (γ.submatrix s id).row = f ∘ Fin.cast hfr.symm := by
      funext i
      exact hs i
    rw [h3]
    exact h2
  have hdet : (γ.submatrix s id).det ≠ 0 := by
    have := Matrix.linearIndependent_rows_iff_isUnit.1 hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  refine ⟨s, ?_⟩
  by_contra hcon
  push_neg at hcon
  apply hv
  set B := γ.submatrix s id with hB
  have hz : Bᵀ.cramer v = 0 := by
    funext k
    rw [cramer_apply, updateCol_transpose, det_transpose]
    exact hcon k
  have h3 := mulVec_cramer Bᵀ v
  rw [hz, mulVec_zero, det_transpose] at h3
  exact (smul_eq_zero.1 h3.symm).resolve_left hdet

variable {E : Type} [Field E] {ι : Type} [Fintype ι] {a : ℕ}

noncomputable def rowMap (ε : ι → E →+* ℂ) (A : ι → Matrix (Fin a) (Fin a) ℂ) (v : Fin a → E) :
    ι → Fin a → ℂ :=
  fun i => (fun j => ε i (v j)) ᵥ* A i

theorem rowMap_sub (ε : ι → E →+* ℂ) (A : ι → Matrix (Fin a) (Fin a) ℂ) (v w : Fin a → E) :
    rowMap ε A (v - w) = rowMap ε A v - rowMap ε A w := by
  funext i
  have : (fun j => ε i (v j - w j)) = (fun j => ε i (v j)) - (fun j => ε i (w j)) := by
    funext j; simp
  simp only [rowMap, Pi.sub_apply]
  rw [this, sub_vecMul]

theorem det_mem_of_entries {E : Type} [Field E] (R : Subring E) {a : ℕ}
    (B : Matrix (Fin a) (Fin a) E) (hB : ∀ r s, B r s ∈ R) : B.det ∈ R := by
  rw [det_apply']
  refine Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) ?_
  exact Subring.prod_mem _ fun i _ => hB _ _

theorem one_le_mul_norm_rowMap (R : Subring E) [Nonempty ι] (ε : ι → E →+* ℂ)
    (hprod : ∀ z ∈ R, z ≠ 0 → 1 ≤ ∏ i, ‖ε i z‖) {d n₀ : ℕ}
    (A : ι → Matrix (Fin a) (Fin a) ℂ) (hA : ∀ i, ‖(A i).det‖ = 1) {T : ℝ} (hT : 0 ≤ T)
    (γ : Matrix (Fin d) (Fin a) E) (hγ : γ.rank = a) (hint : ∀ i j, (n₀ : E) * γ i j ∈ R)
    (hy : ∀ k, ‖rowMap ε A (γ k)‖ ≤ T) (v : Fin a → E) (hv : v ≠ 0)
    (hvint : ∀ j, (n₀ : E) * v j ∈ R) (hn₀ : 0 < n₀) :
    1 ≤ (n₀ : ℝ) ^ a * a.factorial * T ^ (a - 1) * ‖rowMap ε A v‖ := by
  classical
  obtain ⟨s, k, hdet⟩ := exists_exchange γ hγ v hv
  set B := (γ.submatrix s id).updateRow k v with hB
  have hn0E : (n₀ : E) ≠ 0 := by
    have : ((n₀ : ℂ)) ≠ 0 := by exact_mod_cast hn₀.ne'
    intro h
    apply this
    have h2 := congrArg (ε (Classical.arbitrary ι)) h
    simpa using h2
  set m := ‖rowMap ε A v‖ with hm
  set L : ℝ := (n₀ : ℝ) ^ a * a.factorial * T ^ (a - 1) * m with hL
  have hL0 : 0 ≤ L := by positivity
  set z : E := ((n₀ : E) • B).det with hz
  have hzR : z ∈ R := by
    refine det_mem_of_entries R _ fun r c => ?_
    by_cases h : r = k
    · subst h; simpa [hB, updateRow_self] using hvint c
    · simpa [hB, updateRow_ne h] using hint (s r) c
  have hz' : z = (n₀ : E) ^ a * B.det := by
    simp [hz, det_smul]
  have hz0 : z ≠ 0 := by
    rw [hz']; exact mul_ne_zero (pow_ne_zero _ hn0E) hdet
  have hbound : ∀ i, ‖ε i z‖ ≤ L := by
    intro i
    have h1 : ε i B.det = (B.map (ε i)).det := by
      simpa using RingHom.map_det (ε i) B
    have h2 : ‖(B.map (ε i)).det‖ = ‖(B.map (ε i) * A i).det‖ := by
      rw [det_mul, norm_mul, hA i, mul_one]
    have h3 : ‖(B.map (ε i) * A i).det‖ ≤
        a.factorial * ∏ r, (Function.update (fun _ => T) k m) r := by
      refine norm_det_le_factorial_mul_prod _ _ fun r c => ?_
      have hrow : (B.map (ε i) * A i) r c = rowMap ε A (B r) i c := rfl
      rw [hrow]
      by_cases h : r = k
      · subst h
        simp only [hB, updateRow_self, Function.update_self]
        exact (norm_le_pi_norm _ c).trans (norm_le_pi_norm (rowMap ε A v) i)
      · simp only [hB, updateRow_ne h, Function.update_of_ne h]
        exact ((norm_le_pi_norm _ c).trans (norm_le_pi_norm (rowMap ε A _) i)).trans (hy (s r))
    have h4 : ∏ r, (Function.update (fun _ => T) k m) r = m * T ^ (a - 1) := by
      rw [Finset.prod_update_of_mem (Finset.mem_univ k)]
      simp [Finset.card_sdiff]
    rw [h4] at h3
    rw [hz', map_mul, map_pow, norm_mul, norm_pow, h1, h2]
    have h5 : ‖ε i (n₀ : E)‖ = n₀ := by simp
    rw [h5, hL]
    calc (n₀ : ℝ) ^ a * ‖(B.map (ε i) * A i).det‖
        ≤ (n₀ : ℝ) ^ a * (a.factorial * (m * T ^ (a - 1))) := by gcongr
      _ = _ := by ring
  have h6 : 1 ≤ L ^ Fintype.card ι := by
    calc (1 : ℝ) ≤ ∏ i, ‖ε i z‖ := hprod z hzR hz0
      _ ≤ ∏ _i : ι, L := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hbound i
      _ = L ^ Fintype.card ι := by simp [Finset.card_univ]
  by_contra hlt
  push_neg at hlt
  exact absurd h6 (not_le.2 (pow_lt_one₀ hL0 hlt Fintype.card_ne_zero))

theorem card_le_of_rows_le (R : Subring E) [Nonempty ι] (ε : ι → E →+* ℂ)
    (hprod : ∀ z ∈ R, z ≠ 0 → 1 ≤ ∏ i, ‖ε i z‖) {d n₀ : ℕ} (hn₀ : 0 < n₀)
    (A : ι → Matrix (Fin a) (Fin a) ℂ) (hA : ∀ i, ‖(A i).det‖ = 1) {T : ℝ} (hT : 1 ≤ T)
    (F : Finset (Matrix (Fin d) (Fin a) E))
    (hF : ∀ γ ∈ F, γ.rank = a ∧ (∀ i j, (n₀ : E) * γ i j ∈ R) ∧
      ∀ k, ‖rowMap ε A (γ k)‖ ≤ T) :
    (F.card : ℝ) ≤ ((1 + 2 * ((n₀ : ℝ) ^ a * a.factorial)) * T ^ (a + 1)) ^
      (Module.finrank ℝ (ι → Fin a → ℂ) * d) := by
  classical
  have hn₀' : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hT0 : 0 < T := by linarith
  set K : ℝ := (n₀ : ℝ) ^ a * a.factorial with hK
  have hK0 : 0 < K := by positivity
  rcases F.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨hr₀, hi₀, hy₀⟩ := hF γ₀ hγ₀
  set S : Finset (Fin a → E) := F.biUnion (fun γ => Finset.univ.image (fun k => γ k)) with hSdef
  have hS : ∀ x ∈ S, ∃ γ ∈ F, ∃ k, γ k = x := by
    intro x hx
    obtain ⟨γ, hγ, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hx
    exact ⟨γ, hγ, k, hk⟩
  have hSint : ∀ x ∈ S, ∀ j, (n₀ : E) * x j ∈ R := by
    intro x hx j
    obtain ⟨γ, hγ, k, rfl⟩ := hS x hx
    exact (hF γ hγ).2.1 k j
  set δ : ℝ := (K * T ^ (a - 1))⁻¹ with hδdef
  have hδ : 0 < δ := by positivity
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ ‖rowMap ε A x - rowMap ε A y‖ := by
    intro x hx y hy hxy
    have h1 := one_le_mul_norm_rowMap R ε hprod A hA hT0.le γ₀ hr₀ hi₀ hy₀ (x - y)
      (sub_ne_zero.2 hxy) (fun j => by
        have := R.sub_mem (hSint x hx j) (hSint y hy j)
        simpa [mul_sub] using this) hn₀
    rw [rowMap_sub] at h1
    rw [hδdef, inv_le_iff_one_le_mul₀ (by positivity)]
    calc (1 : ℝ) ≤ _ := h1
      _ = _ := by rw [hK]; ring
  have hbd : ∀ x ∈ S, ‖rowMap ε A x‖ ≤ T := by
    intro x hx
    obtain ⟨γ, hγ, k, rfl⟩ := hS x hx
    exact (hF γ hγ).2.2 k
  have hpack := Formalism.SA.P.card_le_of_separated S (rowMap ε A) δ T hδ hT0.le hsep hbd
  have h2 : 1 + 2 * T / δ ≤ (1 + 2 * K) * T ^ (a + 1) := by
    have h3 : T * T ^ (a - 1) ≤ T ^ (a + 1) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (Nat.sub_le _ _)) hT0.le
    have h4 : (1 : ℝ) ≤ T ^ (a + 1) := one_le_pow₀ hT
    have h5 : 2 * T / δ = 2 * K * (T * T ^ (a - 1)) := by
      rw [hδdef, div_inv_eq_mul]; ring
    rw [h5]
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 * K)]
  have hSc : (S.card : ℝ) ≤ ((1 + 2 * K) * T ^ (a + 1)) ^ Module.finrank ℝ (ι → Fin a → ℂ) :=
    hpack.trans (pow_le_pow_left₀ (by positivity) h2 _)
  have hFS : F.card ≤ S.card ^ d := by
    calc F.card ≤ (Fintype.piFinset (fun _ : Fin d => S)).card := by
          refine Finset.card_le_card_of_injOn (fun γ k => γ k) ?_ ?_
          · intro γ hγ
            refine Fintype.mem_piFinset.2 fun k => ?_
            exact Finset.mem_biUnion.2 ⟨γ, hγ, Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩⟩
          · intro γ _ γ' _ h
            ext k j
            exact congrFun (congrFun h k) j
      _ = S.card ^ d := by simp
  calc (F.card : ℝ) ≤ (S.card : ℝ) ^ d := by exact_mod_cast hFS
    _ ≤ (((1 + 2 * K) * T ^ (a + 1)) ^ Module.finrank ℝ (ι → Fin a → ℂ)) ^ d :=
        pow_le_pow_left₀ (by positivity) hSc _
    _ = _ := by rw [pow_mul]

theorem tsum_schwartz_fullRank_le (E : Type) [Field E] (R : Subring E) (ι : Type) [Fintype ι]
    [Nonempty ι] (ε : ι → E →+* ℂ) (hprod : ∀ z ∈ R, z ≠ 0 → 1 ≤ ∏ i, ‖ε i z‖)
    (a d n₀ : ℕ) (hn₀ : 0 < n₀) (φ : SchwartzMap (ι → Fin d → Fin a → ℂ) ℂ) :
    ∃ C : ℝ, ∀ A : ι → Matrix (Fin a) (Fin a) ℂ, (∀ i, ‖(A i).det‖ = 1) →
      ∑' γ : {γ : Matrix (Fin d) (Fin a) E // γ.rank = a ∧ ∀ i j, (n₀ : E) * γ i j ∈ R},
        ‖φ (fun i => (γ.1.map (ε i)) * A i)‖ₑ ≤ ENNReal.ofReal C := by
  classical
  have hn₀' : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  set e : ℕ := Module.finrank ℝ (ι → Fin a → ℂ) * d with he
  set b : ℝ := 1 + 2 * ((n₀ : ℝ) ^ a * a.factorial) with hb
  have hb0 : 0 < b := by positivity
  set M : ℕ := (a + 1) * e with hM
  set Cφ : ℝ := 2 ^ (M + 1) * ((Finset.Iic ((M + 1, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) φ with hCφ
  have hdec : ∀ x, (1 + ‖x‖) ^ (M + 1) * ‖φ x‖ ≤ Cφ := fun x => by
    simpa using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M + 1, 0))
      (k := M + 1) (n := 0) le_rfl le_rfl φ x
  have hC0 : 0 ≤ Cφ := le_trans (by positivity) (hdec 0)
  set Q : ℝ := Cφ * b ^ e * 2 ^ M with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨2 * Q, fun A hA => ?_⟩
  let w : ℕ → ℝ := fun j => Cφ / (2 ^ j) ^ (M + 1)
  let Γ := {γ : Matrix (Fin d) (Fin a) E // γ.rank = a ∧ ∀ i j, (n₀ : E) * γ i j ∈ R}
  let p : ℕ → Γ → Prop := fun j γ => ∀ k, ‖rowMap ε A (γ.1 k)‖ ≤ 2 ^ (j + 1)
  have step1 : ∀ γ : Γ, ‖φ (fun i => (γ.1.map (ε i)) * A i)‖ₑ ≤
      ∑' j, if p j γ then ENNReal.ofReal (w j) else 0 := by
    intro γ
    set y : ι → Fin d → Fin a → ℂ := fun i => (γ.1.map (ε i)) * A i with hy
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := 1 + ‖y‖) (y := (2 : ℝ))
      (by linarith [norm_nonneg y]) one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [if_pos]
    · rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      show ‖φ y‖ ≤ Cφ / (2 ^ j) ^ (M + 1)
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact le_trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hj1 _) (norm_nonneg _)) (hdec y)
    · intro k
      have h1 : ‖rowMap ε A (γ.1 k)‖ ≤ ‖y‖ := by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
        have h2 : rowMap ε A (γ.1 k) i c = y i k c := rfl
        rw [h2]
        exact (norm_le_pi_norm (y i k) c).trans
          ((norm_le_pi_norm (y i) k).trans (norm_le_pi_norm y i))
      linarith
  have step2 : ∀ j, ∑' γ : Γ, (if p j γ then ENNReal.ofReal (w j) else 0) ≤
      ENNReal.ofReal (Q * (1 / 2) ^ j) := by
    intro j
    have hw0 : 0 ≤ w j := by positivity
    have hval : w j * (b * (2 ^ (j + 1) : ℝ) ^ (a + 1)) ^ e = Q * (1 / 2) ^ j := by
      have h1 : (b * (2 ^ (j + 1) : ℝ) ^ (a + 1)) ^ e = b ^ e * 2 ^ M * (2 ^ j) ^ M := by
        rw [mul_pow, mul_assoc, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
        congr 2
        rw [hM]; ring
      have h2 : ((2 : ℝ) ^ j) ^ (M + 1) = (2 ^ j) ^ M * 2 ^ j := pow_succ _ _
      simp only [w]
      rw [h1, h2, hQ, one_div, inv_pow]
      field_simp
    rw [← hval, ENNReal.ofReal_mul hw0, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_right ?_ _
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.card_image_of_injective _ Subtype.val_injective]
    refine card_le_of_rows_le R ε hprod hn₀ A hA (one_le_pow₀ one_le_two) _ ?_
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨g.2.1, g.2.2, (Finset.mem_filter.1 hg).2⟩
  calc ∑' γ : Γ, ‖φ (fun i => (γ.1.map (ε i)) * A i)‖ₑ
      ≤ ∑' γ : Γ, ∑' j, (if p j γ then ENNReal.ofReal (w j) else 0) :=
        ENNReal.tsum_le_tsum step1
    _ = ∑' j, ∑' γ : Γ, (if p j γ then ENNReal.ofReal (w j) else 0) := ENNReal.tsum_comm
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (Q * (1 / 2) ^ j) := ENNReal.tsum_le_tsum step2
    _ = ENNReal.ofReal (∑' j : ℕ, Q * (1 / 2) ^ j) := by
        refine (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) ?_).symm
        exact summable_geometric_two.mul_left Q
    _ = ENNReal.ofReal (2 * Q) := by
        rw [tsum_mul_left, tsum_geometric_two, mul_comm]

end GlobalTheory.CompanionTheory.Twist.FullRank
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.CompanionTheory.Ipf.Bdd
variable {D : D7}

def _root_.GlobalTheory.CompanionTheory.Ipf.mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : Mx D a c :=
  HMul.hMul (x : Matrix (Fin a) (Fin b) (AE D)) (y : Matrix (Fin b) (Fin c) (AE D))

def _root_.GlobalTheory.CompanionTheory.Ipf.rat {a b : ℕ} (γ : Matrix (Fin a) (Fin b) D.host.E) : Mx D a b := γ.map (incA D)

theorem infPart_incA (c : D.host.E) : infPart D (incA D c) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] c := by
  simp [infPart, incA, inclR]

theorem infPart_cA (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem compAt_mulM {m k n : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (A : Mx D m k) (B : Mx D k n) :
    compAt θ τ (mul A B) = compAt θ τ A * compAt θ τ B := by
  unfold compAt mul
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_rat {m k : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (γ : Matrix (Fin m) (Fin k) D.host.E) :
    compAt θ τ (rat γ) = γ.map (tauE D τ) := by
  ext i j
  simp only [compAt, rat, Matrix.map_apply]
  rw [infPart_incA]
  exact (hθ τ).1 _

theorem norm_det_compAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    ‖(compAt θ τ (mt V g)).det‖ = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  set ρ : AE D →+* ℂ := (θ τ).comp (infPart D) with hρ
  have hc : ∀ z, ρ (cA D z) = starRingEnd ℂ (ρ z) := fun z => by
    simp only [hρ, RingHom.comp_apply]
    rw [infPart_cA]
    exact GlobalTheory.Mem.VolExists.infEmb_sigR (GlobalTheory.DefiniteQuotient.cmExt D) (hθ τ) _
  have hd := congrArg (fun M => ρ M.det) h
  simp only [Matrix.det_mul, Matrix.det_transpose, map_mul] at hd
  have e1 : ρ (((mt V g).map (cA D)).det) = starRingEnd ℂ (ρ (mt V g).det) := by
    rw [← hc]
    congr 1
    exact ((cA D).map_det _).symm
  have e2 : ρ (V.gram.map (incA D)).det ≠ 0 := by
    have : (V.gram.map (incA D)).det = incA D V.gram.det := ((incA D).map_det _).symm
    rw [this]
    have : ρ (incA D V.gram.det) = tauE D τ V.gram.det := by
      simp only [hρ, RingHom.comp_apply]
      rw [infPart_incA]
      exact (hθ τ).1 _
    rw [this]
    exact (map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)
  have e3 : (compAt θ τ (mt V g)).det = ρ (mt V g).det := (ρ.map_det _).symm
  rw [e3]
  rw [e1] at hd
  have h4 : starRingEnd ℂ (ρ (mt V g).det) * ρ (mt V g).det = 1 := by
    refine mul_right_cancel₀ e2 ?_
    calc _ = starRingEnd ℂ (ρ (mt V g).det) * ρ (V.gram.map (incA D)).det * ρ (mt V g).det := by ring
      _ = ρ (V.gram.map (incA D)).det := hd
      _ = _ := by ring
  rw [Complex.conj_mul'] at h4
  have h5 : (‖ρ (mt V g).det‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ ‖ρ (mt V g).det‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖ρ (mt V g).det‖ - 1), sq_nonneg (‖ρ (mt V g).det‖ + 1)]

theorem isOpen_nsmul_mem (N : ℕ) :
    IsOpen {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | N • y ∈ intAE D} := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin.addGrpF (F := D.host.F) (E := D.host.E)
  have h1 : IsOpen {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    have e : {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} = {z | ∃ y ∈ intAE D, z = 1 • y} := by
      ext z
      simp
    rw [e]
    exact this
  exact h1.preimage (continuous_nsmul N)

theorem den_one (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) : ∃ N : ℕ, 0 < N ∧ N • z ∈ intAE D := by
  obtain ⟨n, hn, h⟩ := GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE (D := D) z
  exact ⟨n, hn, by rwa [nsmul_eq_mul]⟩

theorem exists_den {K : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, N • x ∈ intAE D := by
  refine hK.induction_on (p := fun S => ∃ N : ℕ, 0 < N ∧ ∀ x ∈ S, N • x ∈ intAE D)
    ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨N, hN, h⟩
    exact ⟨N, hN, fun x hx => h x (hst hx)⟩
  · rintro s t ⟨N, hN, h⟩ ⟨M, hM, h'⟩
    refine ⟨N * M, by positivity, ?_⟩
    rintro x (hx | hx)
    · rw [mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ (h x hx) M
    · rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ (h' x hx) N
  · intro x _
    obtain ⟨N, hN, hx⟩ := den_one x
    exact ⟨_, mem_nhdsWithin_of_mem_nhds ((isOpen_nsmul_mem N).mem_nhds hx), N, hN, fun y hy => hy⟩

def intR (D : D7) : Subring D.host.E := (algebraMap (𝓞 D.host.E) D.host.E).range

theorem mem_intR_of_finPart {a : D.host.E} (h : finPart D (incA D a) ∈ intAE D) : a ∈ intR D := by
  have h1 := (GlobalTheory.SplitDec.rat_int_iff (D := D) a).1 ((GlobalTheory.SplitDec.int_iff _).1 h)
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 h1
  exact ⟨y, hy⟩

theorem one_le_prod_tauE (z : D.host.E) (hz : z ∈ intR D) (h0 : z ≠ 0) : 1 ≤ ∏ τ, ‖tauE D τ z‖ := by
  obtain ⟨r, rfl⟩ := hz
  have h1 := NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 D.host.E) D.host.E r)
  have hb := Formalism.L2.Fam.ThC.plE_bij D
  have h2 : ∏ w : InfinitePlace D.host.E, w (algebraMap (𝓞 D.host.E) D.host.E r) ^ w.mult =
      ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖ ^ 2 := by
    rw [← hb.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [InfinitePlace.mult, if_neg (by simpa [InfinitePlace.isComplex_iff] using Formalism.L2.Fam.ThC.plE_complex τ)]
    rfl
  have hr : r ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ (algebraMap (𝓞 D.host.E) D.host.E r) : ℚ) : ℝ)| := by
    have e := Algebra.coe_norm_int r
    have hn : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr
    have e' : (algebraMap (𝓞 D.host.E) D.host.E r) = (r : D.host.E) := rfl
    rw [e', ← e]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ r| := Int.one_le_abs hn
    have h' : ((1 : ℤ) : ℝ) ≤ ((|Algebra.norm ℤ r| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have h4 : (1 : ℝ) ≤ (∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖) ^ 2 := by
    rw [← Finset.prod_pow, ← h2, h1]
    exact_mod_cast h3
  have h5 : (0 : ℝ) ≤ ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

theorem mul_mem_int {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  rw [GlobalTheory.IdemSupport.mem_intAE_iff] at *
  rw [map_mul]
  exact mul_mem hx hy

theorem exists_den_matrix {a b : ℕ}
    {K : Set (Matrix (Fin a) (Fin b) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m ∈ K, ∀ i j, N • m i j ∈ intAE D := by
  have h : ∀ p : Fin a × Fin b, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ (fun m : Matrix (Fin a) (Fin b) _ => m p.1 p.2) '' K, N • x ∈ intAE D :=
    fun p => exists_den (hK.image (continuous_id.matrix_elem p.1 p.2))
  choose N hN h using h
  refine ⟨∏ p, N p, Finset.prod_pos fun p _ => hN p, fun m hm i j => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i, j)), mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (h (i, j) _ ⟨m, hm, rfl⟩) _

theorem nonempty_tau (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

end GlobalTheory.CompanionTheory.Ipf.Bdd

end
end
