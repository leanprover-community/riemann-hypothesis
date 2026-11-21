import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightLatticeComparison
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HarProjEqZeroIff
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankTensor

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility Formalism.CountingSumsFrames MvPolynomial

def RS.Ov {p n' : ℕ} (R : RS p n') : ValuationSubring R.Kf :=
  { (algebraMap R.O R.Kf).range with
    mem_or_inv_mem' := by
      intro x
      have := R.std.1.frac_O
      rcases ValuationRing.isInteger_or_isInteger R.O x with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact Or.inl ⟨a, ha⟩
      · exact Or.inr ⟨a, ha⟩ }

theorem RS.mem_Ov {p n' : ℕ} (R : RS p n') (a : R.O) : algebraMap R.O R.Kf a ∈ R.Ov.toSubring := ⟨a, rfl⟩

theorem RS.pLocal {p n' : ℕ} (R : RS p n') : PLocal R.Ov.toSubring p := by
  intro n hn
  have hcop : IsCoprime (n : ℤ) (p : ℤ) := by
    have := (Nat.Prime.coprime_iff_not_dvd R.std.1.prime).2 hn
    exact (Nat.isCoprime_iff_coprime.2 this).symm
  obtain ⟨a, b, hab⟩ := hcop
  have hu : IsUnit (n : R.O) := by
    by_contra hnu
    have h1 : (n : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h2 : (p : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 R.p_not_unit
    have h3 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) ∈ IsLocalRing.maximalIdeal R.O :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    have h4 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) = 1 := by
      have := congrArg (fun z : ℤ => (z : R.O)) hab
      simpa using this
    rw [h4] at h3
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 isUnit_one
  obtain ⟨v, hv⟩ := hu
  refine ⟨((v⁻¹ : R.Oˣ) : R.O), ?_⟩
  have h5 : algebraMap R.O R.Kf ((v⁻¹ : R.Oˣ) : R.O) * (n : R.Kf) = 1 := by
    rw [← map_natCast (algebraMap R.O R.Kf) n, ← hv, ← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h5

def TwoLetterModelIdentification : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m →
    ∃ (α : ∀ P Q : ℕ, twoSp R.Kf m P Q ≃ₗ[R.Kf] PolAB R.Kf (m + 1) P Q)
      (β : ∀ a b : ℕ, PolAB R.Kf (m + 1) a b →ₗ[R.Kf] dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b))),
      (∀ a b, Function.Surjective (β a b)) ∧
      (∀ a b (f : PolAB R.Kf (m + 1) a b), β a b f = 0 ↔
        ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), (f : PolXY R.Kf (m + 1)) = hXY R.Kf (m + 1) * G) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∃ g' : GL (Fin (m + 1)) R.Kf,
        (∀ (P Q : ℕ) (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf), x ∈ twoLat R.O m P Q Λ ↔
          ∃ hx : x ∈ twoSp R.Kf m P Q,
            (α P Q ⟨x, hx⟩ : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring)) ∧
        (∀ (a b : ℕ) (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), y ∈ H0 R.O m (wtPQ m a b) Λ ↔
          ∃ f : PolAB R.Kf (m + 1) a b, (f : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring) ∧
            (β a b f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = y)

theorem expo_le (p a m P Q : ℕ) (hp : 2 ≤ p) (h : P + Q + 1 ≤ 8 * a) :
    (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) ≤ ⌈((m : ℝ) + 2) * lgA p a m⌉₊ := by
  have h1 : (Nat.log p (P + Q + (m + 1)) : ℝ) ≤ Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) := Real.natLog_le_logb _ _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have h2 : Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + m) := by
    apply Real.logb_le_logb_of_le hp1
    · have : 0 < P + Q + (m + 1) := by omega
      exact_mod_cast this
    · have : P + Q + (m + 1) ≤ 8 * a + m := by omega
      exact_mod_cast this
  have h3 : (((m + 1 + 1) * Nat.log p (P + Q + (m + 1)) : ℕ) : ℝ) ≤ ((m : ℝ) + 2) * lgA p a m := by
    unfold lgA
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    have : ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hm
  exact_mod_cast le_trans h3 (Nat.le_ceil _)

theorem single_weight_of_model_identification (h : TwoLetterModelIdentification) : SingleWeightLatticeComparison := by
  classical
  intro p n' R m hm a P Q hPQ
  obtain ⟨α, β, hsurj, hker, hlat⟩ := h p n' R m hm
  have : CharZero R.Kf := R.charZero
  have hp := R.std.1.prime
  obtain ⟨io, pr, hsum, hL⟩ := oneTop_abs R.Kf (m + 1) P Q p (by omega) hp R.Ov R.pLocal (α P Q)
    (fun j => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) (fun j => β (P - j) (Q - j))
    (fun j => hsurj _ _) (fun j f => hker _ _ f)
  set E := (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) with hE
  set U := ⌈((m : ℝ) + 2) * lgA p a m⌉₊ with hU
  have hEU : E ≤ U := expo_le p a m P Q hp.two_le hPQ
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hEU
  have hpd : (p : R.Kf) ^ d ∈ R.Ov.toSubring := Subring.pow_mem _ (natCast_mem _ p) d
  have hexI : ∀ j, ∃ I : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf,
      I ∘ₗ (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype =
        (twoSp R.Kf m P Q).subtype ∘ₗ io j := fun j => LinearMap.exists_extend _
  have hexP : ∀ j, ∃ Pj : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
      Pj ∘ₗ (twoSp R.Kf m P Q).subtype =
        (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype ∘ₗ pr j :=
    fun j => LinearMap.exists_extend _
  choose I hI using hexI
  choose Pj hPj using hexP
  have hI' : ∀ j (y : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))),
      I j (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = (io j y : MvPolynomial _ R.Kf) :=
    fun j y => LinearMap.congr_fun (hI j) y
  have hP' : ∀ j (x : twoSp R.Kf m P Q),
      Pj j (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf) = (pr j x : MvPolynomial _ R.Kf) :=
    fun j x => LinearMap.congr_fun (hPj j) x
  refine ⟨I, Pj, ?_, ?_, ?_⟩
  · intro x hx
    have h0 := congrArg (twoSp R.Kf m P Q).subtype (hsum ⟨x, hx⟩)
    rw [map_sum] at h0
    calc ∑ j ∈ Finset.range (min P Q + 1), I j (Pj j x)
        = ∑ j ∈ Finset.range (min P Q + 1), (twoSp R.Kf m P Q).subtype (io j (pr j ⟨x, hx⟩)) :=
          Finset.sum_congr rfl fun j _ => by rw [hP' j ⟨x, hx⟩, hI']; rfl
      _ = x := h0
  · intro j _
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rw [hP' j ⟨x, hx⟩]; exact (pr j ⟨x, hx⟩).2
    · rw [hI' j ⟨y, hy⟩]; exact (io j ⟨y, hy⟩).2
  · intro Λ hΛ j hj
    obtain ⟨g', h1, h2⟩ := hlat Λ hΛ
    obtain ⟨hA, hB⟩ := hL g' j hj
    constructor
    · intro x hx
      obtain ⟨hx2, hx3⟩ := (h1 P Q x).1 hx
      obtain ⟨f, hf, hfe⟩ := hA ⟨x, hx2⟩ hx3
      refine (h2 (P - j) (Q - j) _).2 ⟨((p : R.Kf) ^ d) • f, smul_mem_latOf _ g' hpd hf, ?_⟩
      rw [map_smul, hfe, hP' j ⟨x, hx2⟩, Submodule.coe_smul, Submodule.coe_smul, smul_smul, hd, pow_add, mul_comm]
    · intro y hy
      obtain ⟨f, hf, hfe⟩ := (h2 (P - j) (Q - j) y).1 hy
      have h3 := hB f hf
      have hy2 : y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))) := by
        rw [← hfe]; exact (β (P - j) (Q - j) f).2
      have hyf : (⟨y, hy2⟩ : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) = β (P - j) (Q - j) f :=
        Subtype.ext hfe.symm
      refine (h1 P Q _).2 ⟨?_, ?_⟩
      · rw [hI' j ⟨y, hy2⟩]
        exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2
      · have e : (⟨((p : R.Kf) ^ U) • I j y, by
            rw [hI' j ⟨y, hy2⟩]; exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2⟩ : twoSp R.Kf m P Q) =
            ((p : R.Kf) ^ d) • (((p : R.Kf) ^ E) • io j (β (P - j) (Q - j) f)) := by
          have hIy : I j y = (io j (β (P - j) (Q - j) f) : MvPolynomial _ R.Kf) := by
            rw [← hyf]; exact hI' j ⟨y, hy2⟩
          apply Subtype.ext
          show ((p : R.Kf) ^ U) • I j y = _
          rw [Submodule.coe_smul, Submodule.coe_smul, hIy, smul_smul, hd, pow_add, mul_comm]
        rw [e, map_smul, Submodule.coe_smul]
        exact smul_mem_latOf _ g' hpd h3

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

def covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))

def PsiXY (K : Type) [Field K] (m : ℕ) : PolXY K (m + 1) →ₐ[K] MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) K :=
  aeval (Sum.elim (fun i : Fin (m + 1) => X (true, (i, (0 : Fin (m + 1)))))
    (fun i : Fin (m + 1) => rename (Prod.mk false) (covY K m i)))

def deltaB (K : Type) [Field K] (m : ℕ) :
    MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) K →ₐ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  rename Prod.snd

theorem sum_covY (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) :
    ∑ i : Fin (m + 1), (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) * covY K m i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial (Fin (k + 2) × Fin (k + 2)) K) :=
    Matrix.of fun a c => Fin.cases (X (a, 0)) (fun b : Fin (k + 1) => X (a, b.castSucc)) c
  have h0 : N.det = 0 :=
    Matrix.det_zero_of_column_eq (i := 0) (j := (0 : Fin (k + 1)).succ) (Fin.succ_ne_zero 0).symm
      (fun a => rfl)
  rw [Matrix.det_succ_column_zero] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : N.submatrix i.succAbove Fin.succ =
      fun a b => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (k + 2) × Fin (k + 2)) K) := by
    ext a b
    simp [N]
  have hN0 : N i 0 = X (i, 0) := by simp [N]
  rw [hsub, hN0, covY]
  ring

theorem delta_Psi_h (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) : deltaB K m (PsiXY K m (hXY K (m + 1))) = 0 := by
  have hid : (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id := rfl
  have h1 : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inl i) * X (Sum.inr i))) =
      X (i, 0) * covY K m i := by
    intro i
    simp only [PsiXY, deltaB, map_mul, aeval_X, Sum.elim_inl, Sum.elim_inr, rename_X, rename_rename, hid,
      rename_id, AlgHom.id_apply]
  rw [hXY, map_sum, map_sum, Finset.sum_congr rfl fun i _ => h1 i]
  exact sum_covY K m hm

end Formalism.MainNotions.flipOneThree.Pf

end
end
