import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Scalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.degRank :
    ∀ (n N : ℕ), Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N) ≤ (N + 1) ^ (n * n) := by
  intro n N
  change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
    {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}) ≤ _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _)]
  have key : ∀ m : {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N},
      ∀ i, (m : Fin n × Fin n →₀ ℕ) i < N + 1 := by
    intro m i
    have h1 := Finsupp.le_degree i (m : Fin n × Fin n →₀ ℕ)
    have h2 : Finsupp.degree (m : Fin n × Fin n →₀ ℕ)
        = (m : Fin n × Fin n →₀ ℕ).sum fun _ e => e := rfl
    have h3 := m.2
    simp only [Set.mem_setOf_eq] at h3
    omega
  calc Nat.card {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}
      ≤ Nat.card (Fin n × Fin n → Fin (N + 1)) :=
        Nat.card_le_card_of_injective (fun m i => ⟨(m : Fin n × Fin n →₀ ℕ) i, key m i⟩)
          (by
            intro a b h
            apply Subtype.ext
            ext i
            have := congrArg Fin.val (congrFun h i)
            simpa using this)
    _ = (N + 1) ^ (n * n) := by
      simp [Nat.card_eq_fintype_card, Fintype.card_fun]
end

section
open Matrix UpperTheory.V.Weyl

private theorem prod_fin_castLE_eq_prod_le {M : Type*} [CommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∏ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∏ i : Fin n with i ≤ k, f i := by
  apply Finset.prod_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.coe_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _
    rfl

private theorem sum_fin_castLE_eq_sum_le {M : Type*} [AddCommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∑ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∑ i : Fin n with i ≤ k, f i := by
  apply Finset.sum_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.coe_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _
    rfl

theorem UpperTheory.V.Weyl.minorRtr :
    ∀ (n : ℕ) (k : Fin n) (b : Matrix (Fin n) (Fin n) ℂ), (∀ i j, j < i → b i j = 0) →
      rtr b (minor k) = (∏ i : Fin n with i ≤ k, b i i) • minor k := by
  intro n k b hb
  have hmat : (rtr b).mapMatrix (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) =
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) *
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) => b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map
        (MvPolynomial.C : ℂ →+* Pol n) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, rtr,
      MvPolynomial.aeval_X]
    rw [sum_fin_castLE_eq_sum_le k (fun m => MvPolynomial.X (Fin.castLE k.isLt i, m) *
      MvPolynomial.C (b m (Fin.castLE k.isLt j)))]
    symm
    apply Finset.sum_filter_of_ne
    intro m _ hm
    by_contra hmk
    apply hm
    rw [hb m (Fin.castLE k.isLt j) ?_, map_zero, mul_zero]
    simp only [not_le] at hmk
    rw [Fin.lt_iff_val_lt_val] at hmk ⊢
    simp only [Fin.coe_castLE]
    omega
  have hup : (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).det =
      ∏ i : Fin n with i ≤ k, b i i := by
    rw [Matrix.det_of_upperTriangular, ← prod_fin_castLE_eq_prod_le k (fun i => b i i)]
    · rfl
    · intro i j hij
      simp only [Matrix.of_apply]
      apply hb
      rw [Fin.lt_iff_val_lt_val] at hij ⊢
      simpa using hij
  have hC : ((Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map (MvPolynomial.C : ℂ →+* Pol n)).det =
      MvPolynomial.C (∏ i : Fin n with i ≤ k, b i i) := by
    rw [← hup, RingHom.map_det]
    rfl
  unfold minor
  rw [AlgHom.map_det, hmat, Matrix.det_mul, hC, MvPolynomial.smul_eq_C_mul, mul_comm]
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.minorDeg :
    ∀ (n : ℕ) (k : Fin n), minor k ≠ 0 ∧ (minor k).totalDegree ≤ (k : ℕ) + 1 := by
  intro n k
  constructor
  · intro h
    have h0 := congrArg
      (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℂ) else 0)) h
    rw [minor, RingHom.map_det, map_zero] at h0
    rw [show (RingHom.mapMatrix _) _ = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) from ?_] at h0
    · simp at h0
    · ext i j
      simp [Matrix.one_apply, Fin.castLE_inj]
  · rw [minor, Matrix.det_apply]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.topPol :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) → ∃ f : Pol n, f ≠ 0 ∧ f.totalDegree ≤ n * H ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → rtr b f = (∏ k, b k k ^ ν k) • f := by
  intro n ν hν H hH
  classical
  have hmem : ∀ (h : ℕ) (hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty) (i : Fin n),
      i ∈ Finset.univ.filter (fun i : Fin n => h < ν i) ↔ i ≤ (Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs := by
    intro h hs i
    constructor
    · intro hi
      exact Finset.le_max' _ _ hi
    · intro hi
      have hm := Finset.max'_mem _ hs
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le hm.2 (hν hi)⟩
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Pol n, (∀ h, g h ≠ 0) ∧ (∀ h, (g h).totalDegree ≤ n) ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → ∀ h,
        rtr b (g h) = (∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i) • g h := by
    refine ⟨fun h => if hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty then
      minor ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs) else 1, ?_, ?_, ?_⟩
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]
        exact (minorDeg n _).1
      · simp only [dif_neg hs]
        exact one_ne_zero
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]
        have h1 := (minorDeg n ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs)).2
        have h2 := ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs).isLt
        omega
      · simp only [dif_neg hs, MvPolynomial.totalDegree_one]
        exact Nat.zero_le _
    · intro b hb h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]
        rw [minorRtr n _ b hb]
        congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext i
        rw [hmem h hs i, Finset.mem_filter]
        simp
      · simp only [dif_neg hs]
        rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp
  refine ⟨∏ h ∈ Finset.range H, g h, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun h _ => hg1 h)
  · calc (∏ h ∈ Finset.range H, g h).totalDegree ≤ ∑ h ∈ Finset.range H, (g h).totalDegree :=
          MvPolynomial.totalDegree_finset_prod _ _
      _ ≤ ∑ h ∈ Finset.range H, n := Finset.sum_le_sum (fun h _ => hg2 h)
      _ = n * H := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  · intro b hb
    have key : ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i =
        ∏ k, b k k ^ ν k := by
      calc ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i
          = ∏ h ∈ Finset.range H, ∏ i, (if h < ν i then b i i else 1) := by
            refine Finset.prod_congr rfl (fun h _ => ?_)
            rw [Finset.prod_filter]
        _ = ∏ i, ∏ h ∈ Finset.range H, (if h < ν i then b i i else 1) := Finset.prod_comm
        _ = ∏ k, b k k ^ ν k := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            congr 1
            have hf : (Finset.range H).filter (fun h => h < ν i) = Finset.range (ν i) := by
              ext h
              simp only [Finset.mem_filter, Finset.mem_range]
              have := hH i
              omega
            rw [hf, Finset.card_range]
    rw [map_prod, Finset.prod_congr rfl (fun h _ => hg3 b hb h), ← key]
    simp only [Algebra.smul_def, map_prod, Finset.prod_mul_distrib]
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrMul :
    ∀ (n : ℕ), (∀ f : Pol n, rtr 1 f = f) ∧ ∀ (g h : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), rtr (g * h) f = rtr g (rtr h f) := by
  intro n
  constructor
  · intro f
    have e : (rtr (1 : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n) = AlgHom.id ℂ (Pol n) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [rtr, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']
    rw [e]
    rfl
  · intro g h f
    have e : (rtr (g * h) : Pol n →ₐ[ℂ] Pol n) = (rtr g).comp (rtr h) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      rw [AlgHom.comp_apply]
      simp only [rtr, MvPolynomial.aeval_X, map_sum]
      have hx : ∀ x, (MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ k, MvPolynomial.X (ij.1, k) *
          MvPolynomial.C (g k ij.2)) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
          (MvPolynomial.X (i, x) * MvPolynomial.C (h x j)) =
          ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (g k x * h x j) := by
        intro x
        rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.sum_mul]
        simp only [mul_assoc, ← map_mul]
      simp only [hx, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    rfl
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrDeg :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), (rtr g f).totalDegree ≤ f.totalDegree := by
  intro n g f
  have hY : ∀ ij : Fin n × Fin n,
      (∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2) : MvPolynomial (Fin n × Fin n) ℂ).totalDegree ≤ 1 := by
    intro ij
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  conv_lhs => rw [MvPolynomial.as_sum f]
  simp only [rtr, map_sum, MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hY i)
    _ = s i := mul_one _
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrPoly :
    ∀ (n : ℕ) (f : Pol n) (φ : Pol n →ₗ[ℂ] ℂ), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      φ (rtr g f) = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
  intro n f
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro φ
    refine ⟨MvPolynomial.C (φ (MvPolynomial.C a)), fun g => ?_⟩
    have hc := (rtr g).commutes a
    rw [MvPolynomial.algebraMap_eq] at hc
    rw [hc, MvPolynomial.eval_C]
  | add p q hp hq =>
    intro φ
    obtain ⟨p1, h1⟩ := hp φ
    obtain ⟨p2, h2⟩ := hq φ
    exact ⟨p1 + p2, fun g => by rw [map_add, map_add, h1, h2, map_add]⟩
  | mul_X p ij hp =>
    intro φ
    choose P hP using fun k : Fin n =>
      hp (φ.comp (LinearMap.mulRight ℂ (MvPolynomial.X (ij.1, k) : Pol n)))
    refine ⟨∑ k, MvPolynomial.X (k, ij.2) * P k, fun g => ?_⟩
    have hX : rtr g (MvPolynomial.X ij : Pol n)
        = ∑ k, (MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2) := by
      simp [rtr, MvPolynomial.aeval_X]
    rw [map_mul, hX, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hP k g
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at hk
    rw [show rtr g p * ((MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2))
        = MvPolynomial.C (g k ij.2) * (rtr g p * MvPolynomial.X (ij.1, k)) by ring,
      MvPolynomial.C_mul', map_smul, smul_eq_mul, hk, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.polPre :
    ∀ (n N : ℕ), ∃ (Ξ : Pre n) (e : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N ≃ₗ[ℂ] (Fin Ξ.d → ℂ)),
      ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N),
        (f' : Pol n) = rtr g f → Ξ.mat g *ᵥ e f = e f' := by
  intro n N
  let V := MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N
  have mem : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : V), rtr g (f : Pol n) ∈ V := by
    intro g f
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact (rtrDeg n g f).trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 f.2)
  let R : Matrix (Fin n) (Fin n) ℂ → V →ₗ[ℂ] V := fun g =>
    LinearMap.codRestrict V ((rtr g).toLinearMap.comp V.subtype) (mem g)
  have hR : ∀ g (f : V), ((R g f : V) : Pol n) = rtr g (f : Pol n) := fun g f => rfl
  let b := Module.finBasis ℂ V
  let M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun g => LinearMap.toMatrix b b (R g)
  have hR1 : R 1 = LinearMap.id := by
    ext f
    rw [hR, (rtrMul n).1]
    rfl
  have hRm : ∀ g h, R (g * h) = R g ∘ₗ R h := by
    intro g h
    ext f
    rw [hR, (rtrMul n).2]
    rfl
  let mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    { toFun := M
      map_one' := by
        show LinearMap.toMatrix b b (R 1) = 1
        rw [hR1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        show LinearMap.toMatrix b b (R (g * h)) = LinearMap.toMatrix b b (R g) * LinearMap.toMatrix b b (R h)
        rw [hRm]
        exact LinearMap.toMatrix_comp b b b (R g) (R h) }
  have poly : ∀ i j : Fin (Module.finrank ℂ V), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    intro i j
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
    obtain ⟨p, hp⟩ := rtrPoly n ((b j : V) : Pol n) φ
    refine ⟨p, fun g => ?_⟩
    rw [← hp]
    show LinearMap.toMatrix b b (R g) i j = _
    rw [LinearMap.toMatrix_apply, ← hR, ← b.coord_apply, ← hφ]
    rfl
  refine ⟨⟨Module.finrank ℂ V, mat, poly⟩, b.equivFun, ?_⟩
  intro g f f' hf
  show LinearMap.toMatrix b b (R g) *ᵥ b.repr f = b.repr f'
  rw [LinearMap.toMatrix_mulVec_repr]
  congr 2
  apply Subtype.ext
  rw [hR, hf]
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.existsScalar :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) →
      ∃ Ξ : Pre n, 0 < Ξ.d ∧ Ξ.d ≤ (n * H + 1) ^ (n * n) ∧ Ξ.HasWt fun k => (ν k : ℂ) := by
  intro n ν hν H hH
  obtain ⟨f, hf0, hdeg, hf⟩ := topPol n ν hν H hH
  obtain ⟨Ξ, e, he⟩ := polPre n (n * H)
  let F : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ (n * H) :=
    ⟨f, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hdeg⟩
  have hF : F ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hv : e F ≠ 0 := fun h => hF (e.injective (h.trans e.map_zero.symm))
  have htop : Ξ.IsTop ν (e F) := by
    intro b hb
    rw [he b F ((∏ k, b k k ^ ν k) • F) (hf b hb).symm, map_smul]
  obtain ⟨Ξ', h0, hle, hw⟩ := scalar n Ξ ν (e F) hv htop
  refine ⟨Ξ', h0, hle.trans ?_, hw⟩
  have h1 := e.finrank_eq
  have h2 := degRank n (n * H)
  rw [h1] at h2
  simpa using h2
end
