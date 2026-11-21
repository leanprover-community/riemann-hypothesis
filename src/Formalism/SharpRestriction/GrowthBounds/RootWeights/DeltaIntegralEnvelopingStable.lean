import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorEllPBound

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_char_zero_prime {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  obtain ⟨w, _, p_mem, p_ne, _⟩ := S
  haveI : CharZero O := by
    obtain ⟨q, hq⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O q with hqp | hq0
    · exfalso
      by_cases hdvd : q ∣ p
      · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hdvd
        subst hqp'
        exact p_ne (CharP.cast_eq_zero O q)
      · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr (fun h => hdvd (by subst h; exact dvd_rfl))
        have hu : IsUnit (p : ZMod q) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]; exact Units.isUnit _
        have hu' : IsUnit (p : O) := by
          have h5 := hu.map (ZMod.castHom (dvd_refl q) O)
          simpa using h5
        exact (IsLocalRing.mem_maximalIdeal _).mp p_mem hu'
    · subst hq0
      exact CharP.charP_to_charZero O
  unfold KK
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_scalar {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp [Submodule.mem_iInf, sub_eq_zero]

theorem inv_factorial_prod_eq_choose [CharZero K] (m : ℤ) (k : ℕ) :
    ((k.factorial : K)⁻¹) * ∏ j ∈ range k, ((m : K) - (j : K)) = ((Ring.choose m k : ℤ) : K) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose m k
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  have h2 := congrArg (fun z : ℤ => (z : K)) h1
  push_cast at h2
  rw [h2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]

theorem binomial_diagonal_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (k : ℕ) : binomE E a k x = ((Ring.choose (mu a) k : ℤ) : K) • x := by
  have hx' := (mem_weightSpace_iff_diag_scalar.mp hx) a
  unfold binomE
  rw [LinearMap.smul_apply, ← inv_factorial_prod_eq_choose (mu a) k, mul_smul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx']
    rw [← sub_smul, map_smul, ih, smul_smul]
    congr 1
    ring

def shiftedBinomialOperator (E : GLOps n K V) (a : Fin n) (c : ℤ) (d : ℕ) : Module.End K V :=
  ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : K) • binomE E a ij.1

theorem shifted_binomial_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (c : ℤ) (d : ℕ) : shiftedBinomialOperator E a c d x = ((Ring.choose (mu a + c) d : ℤ) : K) • x := by
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, binomial_diagonal_on_weight hx, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Ring.add_choose_eq d (Commute.all _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro ij _
  ring

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem intCast_smul_mem_submodule (M : Submodule O V) (z : ℤ) {x : V} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem shifted_binomial_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M) (a : Fin n) (c : ℤ)
    (d : ℕ) {x : V} (hx : x ∈ M) : shiftedBinomialOperator E a c d x ∈ M := by
  unfold UZStable at hM
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro ij _
  rw [LinearMap.smul_apply]
  exact intCast_smul_mem_submodule M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)

theorem lattice_stable_weight_separator [CharZero (KK O)] (E : GLOps n (KK O) V) {lam nu : Fin n → ℤ} (h : nu ≠ lam) :
    ∃ (T : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g lam = 1 ∧ g nu = 0 ∧
      (∀ mu, ∀ x ∈ weightSp E mu, T x = ((g mu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, T x ∈ M := by
  have hex : ∃ a, nu a ≠ lam a := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  obtain ⟨a, ha⟩ := hex
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, lam a - nu a = δ := ⟨(lam a - nu a).toNat, by omega⟩
    refine ⟨shiftedBinomialOperator E a (-nu a) δ, fun mu => Ring.choose (mu a + -nu a) δ, ?_, ?_, ?_, ?_⟩
    · show Ring.choose (lam a + -nu a) δ = 1
      rw [show lam a + -nu a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    · show Ring.choose (nu a + -nu a) δ = 0
      rw [show nu a + -nu a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro mu x hx
      exact shifted_binomial_on_weight hx a (-nu a) δ
    · exact fun M hM x hx => shifted_binomial_preserves_lattice hM a (-nu a) δ hx
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, nu a - lam a = δ := ⟨(nu a - lam a).toNat, by omega⟩
    refine ⟨1 - shiftedBinomialOperator E a (-lam a) δ, fun mu => 1 - Ring.choose (mu a + -lam a) δ, ?_, ?_, ?_, ?_⟩
    · show 1 - Ring.choose (lam a + -lam a) δ = 1
      rw [show lam a + -lam a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, sub_zero]
    · show 1 - Ring.choose (nu a + -lam a) δ = 0
      rw [show nu a + -lam a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, sub_self]
    · intro mu x hx
      rw [LinearMap.sub_apply, Module.End.one_apply, shifted_binomial_on_weight hx a (-lam a) δ]
      push_cast
      rw [sub_smul, one_smul]
    · intro M hM x hx
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact M.sub_mem hx (shifted_binomial_preserves_lattice hM a (-lam a) δ hx)

theorem lattice_weight_components_mem [CharZero (KK O)] (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) : lam ∉ F → ∀ (y0 : V) (f : (Fin n → ℤ) → V),
      y0 ∈ weightSp E lam → (∀ nu ∈ F, f nu ∈ weightSp E nu) → y0 + ∑ nu ∈ F, f nu ∈ M → y0 ∈ M := by
  induction F using Finset.induction_on with
  | empty =>
    intro _ y0 f _ _ hmem
    simpa using hmem
  | @insert a F ha ih =>
    intro hl y0 f hy0 hf hmem
    have hal : a ≠ lam := fun h => hl (h ▸ Finset.mem_insert_self a F)
    obtain ⟨T, g', hg1, hg0, hT, hTM⟩ := lattice_stable_weight_separator E hal
    have hlF : lam ∉ F := fun h => hl (Finset.mem_insert_of_mem h)
    have h2 := hTM M hM _ hmem
    rw [map_add, map_sum, Finset.sum_insert ha] at h2
    rw [hT lam y0 hy0, hg1, hT a (f a) (hf a (Finset.mem_insert_self a F)), hg0] at h2
    have h3 : ∀ nu ∈ F, T (f nu) = ((g' nu : ℤ) : KK O) • f nu :=
      fun nu hnu => hT nu (f nu) (hf nu (Finset.mem_insert_of_mem hnu))
    rw [Finset.sum_congr rfl h3] at h2
    simp only [Int.cast_one, one_smul, Int.cast_zero, zero_smul, zero_add] at h2
    exact ih hlF y0 (fun nu => ((g' nu : ℤ) : KK O) • f nu) hy0
      (fun nu hnu => Submodule.smul_mem _ _ (hf nu (Finset.mem_insert_of_mem hnu))) h2

theorem weight_component_decomposition (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (lam : Fin n → ℤ) (y : V) :
    ∃ (y0 : V) (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), lam ∉ F ∧ y0 ∈ weightSp E lam ∧
      (∀ nu ∈ F, f nu ∈ weightSp E nu) ∧ y = y0 + ∑ nu ∈ F, f nu := by
  have hy : y ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).mp hy
  refine ⟨c lam, c.support.erase lam, c, by simp, hc lam, fun nu _ => hc nu, ?_⟩
  rw [← hsum]
  simp only [Finsupp.sum]
  by_cases h : lam ∈ c.support
  · exact (Finset.add_sum_erase _ _ h).symm
  · have h0 : c lam = 0 := by simpa using h
    rw [Finset.erase_eq_self.mpr h, h0, zero_add]

theorem integral_enveloping_preserves_submodule {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  unfold UZmon at hu
  unfold UZStable at hM
  induction hu using Submonoid.closure_induction with
  | mem u hu => exact hM u hu
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem sum_other_weights_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) (hl : lam ∉ F)
    (f : (Fin n → ℤ) → V) (hf : ∀ nu ∈ F, f nu ∈ weightSp E nu) : ∑ nu ∈ F, f nu ∈ otherWts E lam := by
  unfold otherWts
  apply Submodule.sum_mem
  intro nu hnu
  have hne : nu ≠ lam := fun h => hl (h ▸ hnu)
  exact (le_iSup₂ (f := fun mu (_ : mu ∈ {mu | mu ≠ lam}) => weightSp E mu) nu hne) (hf nu hnu)

theorem highest_weight_lattice_bounds [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (lam : Fin n → ℤ) (v : V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (hl : ∀ x, (x ∈ M ∧ x ∈ weightSp E lam) ↔ ∃ c : O, x = c • v) :
    Delta (O := O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := O) E lam v := by
  unfold Delta Nabla
  have hv : v ∈ M := ((hl v).mpr ⟨1, (one_smul O v).symm⟩).1
  constructor
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact integral_enveloping_preserves_submodule hM hu v hv
  · intro x hx u hu
    have hux : u x ∈ M := integral_enveloping_preserves_submodule hM hu x hx
    obtain ⟨y0, F, f, hlF, hy0, hf, hdec⟩ := weight_component_decomposition E hE lam (u x)
    have hy0M : y0 ∈ M := lattice_weight_components_mem E M hM lam F hlF y0 f hy0 hf (by rw [← hdec]; exact hux)
    obtain ⟨c, hc⟩ := (hl y0).mp ⟨hy0M, hy0⟩
    refine ⟨c, ?_⟩
    rw [algebraMap_smul, hdec, hc, add_sub_cancel_left]
    exact sum_other_weights_mem E lam F hlF f hf

end lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def LatticeNablaDeltaBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      (∀ x ∈ Nabla (O := O) E lam v, ((p : O) ^ (N0 n * deF p n (ellWt lam))) • x ∈ Delta (O := O) E v)

theorem highest_weight_lattice_of_first_part (D : Formalism.BasicNotions.D7) (h : LatticeNablaDeltaBound) : NablaDeltaComparisonField D := by
  intro p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI
  refine ⟨h p n' O S hR n lam V E v hI, ?_⟩
  intro M hM _ hl
  have := dvr_fraction_field_char_zero_prime S hR.prime
  exact highest_weight_lattice_bounds E hI.1.2.2 lam v M hM.1 hl

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem gl_rep_commutation_apply {E : GLOps n (KK O) V} (hE : IsGLRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  unfold IsGLRep at hE
  have h := LinearMap.congr_fun (hE.1 a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have key : E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d else 0) x - (if d = a then E c b else 0) x) := by
    rw [← h]; abel
  rw [key]
  split_ifs <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero, zero_sub]) <;> abel

theorem gl_rep_operator_weight_shift {E : GLOps n (KK O) V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a b : Fin n) : E a b x ∈ weightSp E (mu + rootW a b) := by
  classical
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero] at hx ⊢
  intro c
  rw [gl_rep_commutation_apply hE c c a b x, hx c, map_smul]
  simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> subst_vars <;>
    (try simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_zero, add_smul, sub_smul, one_smul,
      zero_smul, smul_zero, sub_zero, add_zero, zero_add, zero_sub]) <;> (try abel) <;> (try simp_all)

theorem mem_weight_sup_exists_finset_sum (E : GLOps n (KK O) V) (Pr : (Fin n → ℤ) → Prop) {x : V}
    (hx : x ∈ ⨆ mu, ⨆ (_ : Pr mu), weightSp E mu) :
    ∃ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, Pr mu ∧ f mu ∈ weightSp E mu) ∧
      x = ∑ mu ∈ F, f mu := by
  classical
  let C : V → Prop := fun y => ∃ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
    (∀ mu ∈ F, Pr mu ∧ f mu ∈ weightSp E mu) ∧ y = ∑ mu ∈ F, f mu
  have hmem : ∀ mu, ∀ y ∈ ⨆ (_ : Pr mu), weightSp E mu, C y := by
    intro mu y hy
    dsimp only [C]
    by_cases hP : Pr mu
    · refine ⟨{mu}, fun _ => y, ?_, by simp⟩
      intro nu hnu
      rw [Finset.mem_singleton] at hnu
      subst hnu
      rw [iSup_pos hP] at hy
      exact ⟨hP, hy⟩
    · rw [iSup_neg hP] at hy
      refine ⟨∅, fun _ => 0, by simp, ?_⟩
      simp [(Submodule.mem_bot _).mp hy]
  have hzero : C 0 := ⟨∅, fun _ => 0, by simp, by simp⟩
  have hadd : ∀ y z, C y → C z → C (y + z) := by
    intro y z hy hz
    dsimp only [C] at hy hz ⊢
    obtain ⟨F1, f1, h1, rfl⟩ := hy
    obtain ⟨F2, f2, h2, rfl⟩ := hz
    refine ⟨F1 ∪ F2, fun mu => (if mu ∈ F1 then f1 mu else 0) + (if mu ∈ F2 then f2 mu else 0), ?_, ?_⟩
    · intro mu hmu
      have hPr : Pr mu := by
        rcases Finset.mem_union.mp hmu with h | h
        · exact (h1 mu h).1
        · exact (h2 mu h).1
      refine ⟨hPr, Submodule.add_mem _ ?_ ?_⟩
      · split_ifs with h
        · exact (h1 mu h).2
        · exact Submodule.zero_mem _
      · split_ifs with h
        · exact (h2 mu h).2
        · exact Submodule.zero_mem _
    · rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
        Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
  first
  | exact Submodule.iSup_induction (motive := C) _ hx hmem hzero hadd
  | exact Submodule.iSup_induction (C := C) _ hx hmem hzero hadd

theorem weight_support_sum_eq_zero [CharZero (KK O)] (E : GLOps n (KK O) V) (Pr : (Fin n → ℤ) → Prop) {nu : Fin n → ℤ} {x : V}
    (hx : x ∈ weightSp E nu) (hx2 : x ∈ ⨆ mu, ⨆ (_ : Pr mu), weightSp E mu) (hn : ¬ Pr nu) : x = 0 := by
  classical
  have hwt : ∀ (a : Fin n) (mu : Fin n → ℤ) (y : V), y ∈ weightSp E mu → E a a y = ((mu a : ℤ) : KK O) • y := by
    intro a mu y hy
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hy
    exact hy a
  have key : ∀ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, mu ≠ nu) →
      (∀ mu ∈ F, f mu ∈ weightSp E mu) → ∑ mu ∈ F, f mu ∈ weightSp E nu → ∑ mu ∈ F, f mu = 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro f _ _ _; simp
    | insert mu0 F hmu0 ih =>
      intro f hF hw hs
      have hne : mu0 ≠ nu := hF mu0 (Finset.mem_insert_self _ _)
      obtain ⟨a, ha⟩ : ∃ a, mu0 a ≠ nu a := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      let g : (Fin n → ℤ) → V := fun mu => (((mu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • f mu
      have hES : ∑ mu ∈ insert mu0 F, E a a (f mu) = ∑ mu ∈ insert mu0 F, ((mu a : ℤ) : KK O) • f mu :=
        Finset.sum_congr rfl (fun mu hmu => hwt a mu (f mu) (hw mu hmu))
      have hkey : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • ∑ mu ∈ insert mu0 F, f mu = ∑ mu ∈ F, g mu := by
        have h1 : E a a (∑ mu ∈ insert mu0 F, f mu) = ((nu a : ℤ) : KK O) • ∑ mu ∈ insert mu0 F, f mu :=
          hwt a nu _ hs
        rw [sub_smul, ← h1, map_sum, hES]
        simp only [g, sub_smul, Finset.sum_sub_distrib]
        rw [Finset.sum_insert hmu0, Finset.sum_insert hmu0, smul_add, Finset.smul_sum]
        abel
      have hg : ∀ mu ∈ F, g mu ∈ weightSp E mu := fun mu hmu =>
        Submodule.smul_mem _ _ (hw mu (Finset.mem_insert_of_mem hmu))
      have hF' : ∀ mu ∈ F, mu ≠ nu := fun mu hmu => hF mu (Finset.mem_insert_of_mem hmu)
      have hmemnu : ∑ mu ∈ F, g mu ∈ weightSp E nu := by
        rw [← hkey]
        exact Submodule.smul_mem _ _ hs
      have h0 := ih g hF' hg hmemnu
      rw [← hkey] at h0
      have hc : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => ha (Int.cast_injective h).symm
      exact (smul_eq_zero.mp h0).resolve_left hc
  obtain ⟨F, f, hf, rfl⟩ := mem_weight_sup_exists_finset_sum E Pr hx2
  exact key F f (fun mu hmu h => hn (h ▸ (hf mu hmu).1)) (fun mu hmu => (hf mu hmu).2) hx

theorem stable_enveloping_monoid_mem {E : GLOps n (KK O) V} {W : Submodule (KK O) V} (hW : ∀ a b, ∀ y ∈ W, E a b y ∈ W)
    {u : Module.End (KK O) V} (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  intro x hx
  unfold Umon at hu
  induction hu using Submonoid.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨ab, rfl⟩ := hg
    exact hW ab.1 ab.2 x hx
  | one => simpa using hx
  | mul g g' _ _ ihg ihg' =>
    exact ihg _ (ihg' x hx)

theorem irreducible_stable_contains_eq_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {W : Submodule (KK O) V} (hW : ∀ a b, ∀ y ∈ W, E a b y ∈ W) (hv : v ∈ W) : W = ⊤ := by
  have hI' := hI
  unfold IsIrrHW at hI'
  apply eq_top_iff.mpr
  rw [← hI'.2.2.2, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  exact stable_enveloping_monoid_mem hW hu v hv

theorem irreducible_highest_weight_findim {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    FiniteDimensional (KK O) V := by
  have hI' := hI
  unfold IsIrrHW IsGLRep at hI'
  obtain ⟨W, hWf, hvW, hWst⟩ := hI'.1.2.1 v
  have hW : W = ⊤ := irreducible_stable_contains_eq_top hI hWst hvW
  subst hW
  exact LinearEquiv.finiteDimensional Submodule.topEquiv

def loweringOperatorMonoid (E : GLOps n (KK O) V) : Submonoid (Module.End (KK O) V) :=
  Submonoid.closure {g | ∃ a b : Fin n, b < a ∧ g = E a b}

theorem irreducible_lowering_span_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} = ⊤ := by
  classical
  have hI' := hI
  unfold IsIrrHW IsHWV at hI'
  obtain ⟨hE, _, ⟨_, hvw, hraise⟩, _⟩ := hI'
  have hvw' : ∀ a, E a a v = ((lam a : ℤ) : KK O) • v := by
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hvw
    exact hvw
  have hvS : ∀ u ∈ loweringOperatorMonoid E, u v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := fun u hu => Submodule.subset_span ⟨u, hu, rfl⟩
  have hv1 : v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := hvS 1 (Submonoid.one_mem _)
  have hlow : ∀ c d : Fin n, d < c → ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E c d y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro c d hdc y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨E c d * u, Submonoid.mul_mem _ ?_ hu, rfl⟩
      unfold loweringOperatorMonoid
      exact Submonoid.subset_closure ⟨c, d, hdc, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy
  have hall : ∀ u ∈ loweringOperatorMonoid E, ∀ a b, E a b (u v) ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro u hu
    unfold loweringOperatorMonoid at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro a b
      rw [Module.End.one_apply]
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [hraise a b hab]
        exact Submodule.zero_mem _
      · rw [hvw' a]
        exact Submodule.smul_mem _ _ hv1
      · exact hlow a b hab v hv1
    | mul_left g hg u' _ ih =>
      intro a b
      obtain ⟨c, d, hdc, rfl⟩ := hg
      rw [Module.End.mul_apply, gl_rep_commutation_apply hE a b c d]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (hlow c d hdc _ (ih a b)) ?_) ?_
      · split_ifs
        · exact ih a d
        · exact Submodule.zero_mem _
      · split_ifs
        · exact ih c b
        · exact Submodule.zero_mem _
  have hstab : ∀ a b, ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E a b y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro a b y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      exact hall u hu a b
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy
  exact irreducible_stable_contains_eq_top hI hstab hv1

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def weightHeightAscending (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weightHeightAscending_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightAscending (nu + rootW a b) = weightHeightAscending nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightAscending rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem irreducible_lowering_word_weight [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {u : Module.End (KK O) V} (hu : u ∈ loweringOperatorMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((nu = lam ∧ u v = v) ∨ weightHeightAscending lam < weightHeightAscending nu) ∧
      nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  have hE : IsGLRep E := hI.1
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  unfold loweringOperatorMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact ⟨lam, hv, Or.inl ⟨rfl, rfl⟩, le_rfl, le_rfl⟩
  | mul_left g hg w _ ih =>
    obtain ⟨a, b, hba, rfl⟩ := hg
    obtain ⟨nu, hnu, hor, h0, hl⟩ := ih
    refine ⟨nu + rootW a b, gl_rep_operator_weight_shift hE hnu a b, Or.inr ?_, ?_, ?_⟩
    · have hab : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast hba
      rw [weightHeightAscending_add_root]
      rcases hor with ⟨rfl, -⟩ | h
      · linarith
      · linarith
    · have ha0 : a ≠ 0 := by
        intro h; rw [h] at hba; exact absurd hba (Fin.not_lt_zero _)
      have : (nu + rootW a b) 0 ≤ nu 0 := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm ha0)]
        split_ifs <;> omega
      exact this.trans h0
    · have hbl : b ≠ lastIdx n := by
        intro h
        have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.isLt
        have hb : (b : ℕ) = n - 1 := by rw [h]; rfl
        have : (b : ℕ) < (a : ℕ) := hba
        omega
      have : nu (lastIdx n) ≤ (nu + rootW a b) (lastIdx n) := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm hbl)]
        split_ifs <;> omega
      exact hl.trans this

theorem top_le_line_sup_higher_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ Submodule.span (KK O) {v} ⊔ ⨆ nu, ⨆ (_ : weightHeightAscending lam < weightHeightAscending nu), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, h1 | h1, -⟩ := irreducible_lowering_word_weight hI hu
  · rw [h1.2]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h1 hnu))

theorem top_le_end_bounded_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ ⨆ nu, ⨆ (_ : nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n)), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, -, h0, hl⟩ := irreducible_lowering_word_weight hI hu
  exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem ⟨h0, hl⟩ hnu)

theorem irreducible_weight_end_bounds [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) :
    nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  by_contra hn
  exact h0 (weight_support_sum_eq_zero E (fun mu => mu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ mu (lastIdx n)) hx
    (top_le_end_bounded_weights hI Submodule.mem_top) hn)

theorem irreducible_highest_weight_line [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {x : V} (hx : x ∈ weightSp E lam) : ∃ c : KK O, x = c • v := by
  have hx2 := top_le_line_sup_higher_weights hI (Submodule.mem_top (x := x))
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  have hzw : z ∈ weightSp E lam := by
    have e : z = (c • v + z) - c • v := by abel
    rw [e]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ c hv)
  have hz0 : z = 0 := weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  exact ⟨c, by rw [hz0, add_zero]⟩

theorem highest_line_isCompl_other_weights [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : IsCompl (Submodule.span (KK O) {v}) (otherWts E lam) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact weight_support_sum_eq_zero E (fun mu => mu ∈ {mu | mu ≠ lam}) (Submodule.smul_mem _ c hI.2.2.1.2.1) hx2
      (fun h => h rfl)
  · rw [codisjoint_iff, eq_top_iff, ← hI.1.2.2, iSup_le_iff]
    intro mu x hx
    by_cases h : mu = lam
    · subst h
      obtain ⟨c, rfl⟩ := irreducible_highest_weight_line hI hx
      exact Submodule.mem_sup_left (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v))
    · apply Submodule.mem_sup_right
      show x ∈ ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu
      exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem h hx)

theorem exists_highest_coordinate_functional [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : ∃ xi : V →ₗ[KK O] KK O, xi v = 1 ∧ (∀ w ∈ otherWts E lam, xi w = 0) ∧
      ∀ x, x - xi x • v ∈ otherWts E lam := by
  have hc := highest_line_isCompl_other_weights hI
  have hv0 : v ≠ 0 := hI.2.2.1.1
  let P := Submodule.linearProjOfIsCompl _ _ hc
  let e := LinearEquiv.toSpanNonzeroSingleton (KK O) V v hv0
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_, ?_⟩
  · have h1 : P v = ⟨v, Submodule.mem_span_singleton_self v⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨v, Submodule.mem_span_singleton_self v⟩
    show e.symm (P v) = 1
    rw [h1, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  · intro w hw
    have h2 : P w = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
    show e.symm (P w) = 0
    rw [h2, map_zero]
  · intro x
    have h8 : ∀ s : KK O, ((e s : Submodule.span (KK O) {v}) : V) = s • v := fun s => by
      first
        | rfl
        | simp [e, LinearEquiv.toSpanNonzeroSingleton_apply]
    have h3 : (e.symm (P x)) • v = (P x : V) := by
      rw [← h8, LinearEquiv.apply_symm_apply]
    show x - (e.symm (P x)) • v ∈ otherWts E lam
    rw [h3]
    have hPP : P (P x : V) = P x := Submodule.linearProjOfIsCompl_apply_left hc (P x)
    have h5 : P (x - (P x : V)) = 0 := by
      rw [map_sub, hPP, sub_self]
    have h6 := LinearMap.mem_ker.mpr h5
    have h7 := Submodule.linearProjOfIsCompl_ker hc
    rw [SetLike.ext_iff] at h7
    exact (h7 _).mp h6

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem gl_operator_mem_integral_enveloping (E : GLOps n (KK O) V) (a b : Fin n) : E a b ∈ UZmon E := by
  rw [UZmon.eq_1]
  apply Submonoid.subset_closure
  simp only [UZgens.eq_1, Set.mem_setOf_eq]
  by_cases hab : a = b
  · subst hab
    right
    exact ⟨a, 1, by simp [binomE.eq_1]⟩
  · left
    exact ⟨a, b, 1, hab, by simp [divPowE.eq_1]⟩

theorem enveloping_le_integral_enveloping (E : GLOps n (KK O) V) : Umon E ≤ UZmon E := by
  rw [Umon.eq_1, Submonoid.closure_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact gl_operator_mem_integral_enveloping E a b

theorem mem_nabla_iff_coordinate_integral {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) (x : V) :
    x ∈ Nabla (O := O) E lam v ↔ ∀ u ∈ UZmon E, ∃ c : O, xi (u x) = algebraMap O (KK O) c := by
  rw [Nabla.eq_1, Set.mem_setOf_eq]
  constructor
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h2 _ hc
    rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, sub_eq_zero] at h
    exact h
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h3 (u x)
    rw [hc] at h
    exact h

theorem enveloping_coordinate_separates [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1) {x : V} (hx : ∀ u ∈ UZmon E, xi (u x) = 0) : x = 0 := by
  classical

  let W : Submodule (KK O) V := ⨅ u : UZmon E, LinearMap.ker (xi ∘ₗ (u : Module.End (KK O) V))
  have hmemW : ∀ y, y ∈ W ↔ ∀ u ∈ UZmon E, xi (u y) = 0 := by
    intro y
    rw [Submodule.mem_iInf]
    constructor
    · intro h u hu
      have h' := h ⟨u, hu⟩
      rwa [LinearMap.mem_ker, LinearMap.comp_apply] at h'
    · intro h u
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact h u.1 u.2
  have hxW : x ∈ W := (hmemW x).2 hx
  have hWst : ∀ a b, ∀ y ∈ W, E a b y ∈ W := by
    intro a b y hy
    rw [hmemW] at hy ⊢
    intro u hu
    have h' := hy (u * E a b) (Submonoid.mul_mem _ hu (gl_operator_mem_integral_enveloping E a b))
    rwa [Module.End.mul_apply] at h'
  have hvW : v ∉ W := by
    intro h
    have h' := (hmemW v).1 h 1 (Submonoid.one_mem _)
    rw [Module.End.one_apply, h1] at h'
    exact one_ne_zero h'
  obtain ⟨W', hC, hW'st⟩ := hCR W hWst
  have hv2 : v ∈ W ⊔ W' := by
    rw [hC.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', hvs⟩ := Submodule.mem_sup.mp hv2
  have hv := hI.2.2.1
  have hvw : ∀ a, E a a v = (lam a : KK O) • v := by
    intro a
    have h1' := (Submodule.mem_iInf _).mp hv.2.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1'
    simpa using h1'

  have hww : w ∈ weightSp E lam := by
    unfold weightSp
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hd : E a a w - (lam a : KK O) • w ∈ W := sub_mem (hWst a a w hw) (Submodule.smul_mem W _ hw)
    have hd' : E a a w' - (lam a : KK O) • w' ∈ W' :=
      sub_mem (hW'st a a w' hw') (Submodule.smul_mem W' _ hw')
    have hsum : (E a a w - (lam a : KK O) • w) + (E a a w' - (lam a : KK O) • w') = 0 := by
      have h2 := hvw a
      rw [← hvs, map_add, smul_add] at h2
      rw [sub_add_sub_comm, h2, sub_self]
    have hneg : E a a w - (lam a : KK O) • w ∈ W' := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact W'.neg_mem hd'
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hd hneg

  have hmem := top_le_line_sup_higher_weights hI (Submodule.mem_top : w ∈ (⊤ : Submodule (KK O) V))
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hzw : z ∈ weightSp E lam := by
    have e : z = w - c • v := by
      rw [← hyz]
      abel
    rw [e]
    exact sub_mem hww (Submodule.smul_mem _ c hv.2.1)
  have hz0 : z = 0 :=
    weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  have hwc : w = c • v := by
    rw [← hyz, hz0, add_zero]
  have hc0 : c = 0 := by
    by_contra hc
    apply hvW
    have e : v = c⁻¹ • w := by
      rw [hwc, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e]
    exact Submodule.smul_mem W _ hw
  have hvW' : v ∈ W' := by
    rw [hwc, hc0, zero_smul, zero_add] at hvs
    rw [← hvs]
    exact hw'
  have htop := irreducible_stable_contains_eq_top hI hW'st hvW'
  have hxW' : x ∈ W' := by
    rw [htop]
    exact Submodule.mem_top
  exact (Submodule.disjoint_def.mp hC.disjoint) x hxW hxW'

theorem lattice_fg_of_integral_functionals {W : Type*} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (N : Submodule O W) (Xi : Set (W →ₗ[KK O] KK O))
    (hsep : ∀ w, (∀ ξ ∈ Xi, ξ w = 0) → w = 0)
    (hint : ∀ ξ ∈ Xi, ∀ w ∈ N, ∃ c : O, ξ w = algebraMap O (KK O) c) : N.FG := by
  classical
  obtain ⟨b, hbXi, hbspan, hbli⟩ := exists_linearIndependent (KK O) Xi
  have hbfin : b.Finite := hbli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hbsep : ∀ w : W, (∀ ξ ∈ b, ξ w = 0) → w = 0 := by
    intro w hw
    apply hsep
    intro ξ hξ
    have hle' : Submodule.span (KK O) b ≤ LinearMap.ker (Module.Dual.eval (KK O) W w) := by
      rw [Submodule.span_le]
      intro η hη
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      exact hw η hη
    have hmem : ξ ∈ Submodule.span (KK O) b := by
      rw [hbspan]
      exact Submodule.subset_span hξ
    have h := hle' hmem
    simpa using h
  let Φ : W →ₗ[O] (b → KK O) := LinearMap.pi fun ξ => (ξ.1).restrictScalars O
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro w hw
    apply hbsep
    intro ξ hξ
    have h := congrFun hw ⟨ξ, hξ⟩
    simpa [Φ] using h
  let g : (b → O) →ₗ[O] (b → KK O) :=
    LinearMap.pi fun i => (Algebra.linearMap O (KK O)).comp (LinearMap.proj i)
  have hle : N.map Φ ≤ LinearMap.range g := by
    rintro _ ⟨w, hw, rfl⟩
    choose c hc using fun ξ : b => hint ξ.1 (hbXi ξ.2) w hw
    rw [LinearMap.mem_range]
    refine ⟨c, ?_⟩
    funext ξ
    simp [g, Φ, hc]
  apply Submodule.fg_of_fg_map_injective Φ hΦ
  have hQ : ((N.map Φ).comap g).FG := IsNoetherian.noetherian _
  have h := hQ.map g
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at h

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem findim_exists_finite_weights [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V)
    (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) :
    ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu := by
  have hc := (Submodule.fg_iff_compact (⊤ : Submodule (KK O) V)).1 Module.Finite.fg_top
  first
  | exact IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge
  | exact IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge

theorem linear_map_ext_on_weights {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {W : Type*} [AddCommGroup W] [Module (KK O) W]
    {A B : V →ₗ[KK O] W} (h : ∀ nu ∈ F, ∀ x ∈ weightSp E nu, A x = B x) : A = B := by
  have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (A - B) := by
    refine iSup₂_le fun nu hnu x hx => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h nu hnu x hx
  ext x
  have hx : x ∈ LinearMap.ker (A - B) := hle (hF (Submodule.mem_top : x ∈ (⊤ : Submodule (KK O) V)))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
  exact hx

theorem exists_integral_weight_projection [CharZero (KK O)] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (F : Finset (Fin n → ℤ)) :
    ∃ (P : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧ (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧
      (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P x ∈ M := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, fun _ => 1, rfl, by simp, by simp, fun M _ x hx => by simpa using hx⟩
  | insert nu0 F _ ih =>
    obtain ⟨P, g, g1, g0, hP, hPM⟩ := ih
    by_cases h : nu0 = mu
    · refine ⟨P, g, g1, ?_, hP, hPM⟩
      intro nu hnu hne
      rcases mem_insert.1 hnu with rfl | h2
      · exact absurd h hne
      · exact g0 nu h2 hne
    · obtain ⟨T, g', g'1, g'0, hT, hTM⟩ := lattice_stable_weight_separator (O := O) E h
      refine ⟨T * P, fun nu => g' nu * g nu, by simp [g1, g'1], ?_, ?_, ?_⟩
      · intro nu hnu hne
        rcases mem_insert.1 hnu with rfl | h2
        · simp [g'0]
        · simp [g0 nu h2 hne]
      · intro nu x hx
        rw [Module.End.mul_apply, hP nu x hx, map_smul, hT nu x hx, smul_smul]
        push_cast
        rw [mul_comm]
      · intro M hM x hx
        exact hTM M hM _ (hPM M hM x hx)

theorem exists_integral_weight_projections [CharZero (KK O)] (E : GLOps n (KK O) V) (F : Finset (Fin n → ℤ)) :
    ∃ P : (Fin n → ℤ) → Module.End (KK O) V,
      (∀ mu, ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P mu x ∈ M) ∧
      (∀ mu, ∀ x ∈ weightSp E mu, P mu x = x) ∧
      (∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) := by
  choose P g hg1 hg0 hgw hgM using fun mu => exists_integral_weight_projection E mu F
  refine ⟨P, fun mu M hM x hx => hgM mu M hM x hx, fun mu x hx => ?_, fun mu nu hnu hne x hx => ?_⟩
  · rw [hgw mu mu x hx, hg1 mu]
    simp
  · rw [hgw mu nu x hx, hg0 mu nu hnu hne]
    simp

theorem sum_weight_projections_eq_one {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) : ∑ mu ∈ F, P mu = 1 := by
  refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single nu (fun mu _ hne => h0 mu nu hnu (Ne.symm hne) x hx)
    (fun h => absurd hnu h)]
  rw [h1 nu x hx]
  rfl

private theorem end_mul_apply' (f g : Module.End (KK O) V) (x : V) : (f * g) x = f (g x) := rfl

private theorem diagonal_apply_of_mem_weightSp {E : GLOps n (KK O) V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) : E a a x = ((mu a : ℤ) : KK O) • x := by
  rw [weightSp, Submodule.mem_iInf] at hx
  have h := LinearMap.mem_ker.1 (hx a)
  rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply] at h
  exact h

theorem diagonal_weight_projection_comm {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu : Fin n → ℤ) (a : Fin n) :
    E a a * P mu = (mu a : KK O) • P mu ∧ P mu * E a a = (mu a : KK O) • P mu := by
  constructor
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    by_cases h : nu = mu
    · subst h
      rw [end_mul_apply', LinearMap.smul_apply, h1 _ x hx]
      exact diagonal_apply_of_mem_weightSp hx a
    · rw [end_mul_apply', LinearMap.smul_apply, h0 mu nu hnu h x hx, map_zero, smul_zero]
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    rw [end_mul_apply', LinearMap.smul_apply, diagonal_apply_of_mem_weightSp hx a, map_smul]
    by_cases h : nu = mu
    · subst h
      rw [h1 _ x hx]
    · rw [h0 mu nu hnu h x hx, smul_zero, smul_zero]

def adjointEndAction (E : GLOps n (KK O) V) : GLOps n (KK O) (Module.End (KK O) V) :=
  fun a b => LinearMap.mulLeft (KK O) (E a b) - LinearMap.mulRight (KK O) (E a b)

theorem adjointEndAction_apply (E : GLOps n (KK O) V) (a b : Fin n) (f : Module.End (KK O) V) :
    adjointEndAction E a b f = E a b * f - f * E a b := by
  first
  | rfl
  | simp [adjointEndAction]

private theorem end_one_apply {W : Type*} [AddCommGroup W] [Module (KK O) W] (x : W) :
    (1 : Module.End (KK O) W) x = x := rfl

theorem weight_block_adjoint_weight {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu nu : Fin n → ℤ)
    (f : Module.End (KK O) V) : P mu * f * P nu ∈ weightSp (adjointEndAction E) (mu - nu) := by
  rw [weightSp, Submodule.mem_iInf]
  intro a
  obtain ⟨hm, -⟩ := diagonal_weight_projection_comm hF h1 h0 mu a
  obtain ⟨-, hn⟩ := diagonal_weight_projection_comm hF h1 h0 nu a
  have e1 : E a a * (P mu * f * P nu) = ((mu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [← mul_assoc, ← mul_assoc, hm, smul_mul_assoc, smul_mul_assoc]
  have e2 : P mu * f * P nu * E a a = ((nu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [mul_assoc, hn, mul_smul_comm]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, adjointEndAction_apply, LinearMap.smul_apply, end_one_apply,
    e1, e2, Pi.sub_apply, Int.cast_sub, sub_smul]

theorem endomorphism_sum_weight_blocks {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (f : Module.End (KK O) V) :
    f = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
  have hs := sum_weight_projections_eq_one hF h1 h0
  calc f = (∑ mu ∈ F, P mu) * f * (∑ nu ∈ F, P nu) := by rw [hs, one_mul, mul_one]
    _ = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem adjoint_end_isGLRep [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E) :
    IsGLRep (adjointEndAction E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun f => ?_
    have hr := hE.1 a b c d
    have key : (adjointEndAction E a b * adjointEndAction E c d - adjointEndAction E c d * adjointEndAction E a b) f =
        (E a b * E c d - E c d * E a b) * f - f * (E a b * E c d - E c d * E a b) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, adjointEndAction_apply]
      noncomm_ring
    rw [key, hr]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, adjointEndAction_apply] <;> noncomm_ring
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · obtain ⟨F, hF⟩ := findim_exists_finite_weights E hE.2.2
    obtain ⟨P, -, h1, h0⟩ := exists_integral_weight_projections (O := O) E F
    rw [eq_top_iff]
    intro f _
    rw [endomorphism_sum_weight_blocks hF h1 h0 f]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun nu _ => ?_
    exact Submodule.mem_iSup_of_mem (mu - nu) (weight_block_adjoint_weight hF h1 h0 mu nu f)

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def nablaToDeltaMaps (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O (Module.End (KK O) V) where
  carrier := {f | ∀ x ∈ Nabla (O := O) E lam v, f x ∈ Delta (O := O) E v}
  zero_mem' := fun x _ => by simp
  add_mem' := fun {f g} hf hg x hx => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (hf x hx)

theorem nabla_integral_enveloping_stable (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) :
    UZStable (O := O) E (NablaSub (O := O) E lam v) := by
  intro u hu x hx u' hu'
  exact hx (u' * u) (Submonoid.mul_mem _ hu' (Submonoid.subset_closure hu))

theorem delta_integral_enveloping_stable (E : GLOps n (KK O) V) (v : V) : UZStable (O := O) E (Delta (O := O) E v) := by
  intro u hu x hx
  have hle : Delta (O := O) E v ≤ (Delta (O := O) E v).comap (u.restrictScalars O) := by
    unfold Delta
    rw [Submodule.span_le]
    rintro _ ⟨u', hu', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    exact Submodule.subset_span ⟨u * u', Submonoid.mul_mem _ (Submonoid.subset_closure hu) hu', rfl⟩
  exact hle hx

theorem adjoint_divided_power_expansion [CharZero (KK O)] (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) (f : Module.End (KK O) V) :
    divPowE (adjointEndAction E) a b k f =
      ∑ m ∈ range (k + 1), ((-1 : KK O) ^ (k - m)) • (divPowE E a b m * f * divPowE E a b (k - m)) := by
  have hc : Commute (LinearMap.mulLeft (KK O) (E a b)) ((-1 : KK O) • LinearMap.mulRight (KK O) (E a b)) :=
    (LinearMap.commute_mulLeft_right _ _).smul_right _
  have hsub : adjointEndAction E a b =
      LinearMap.mulLeft (KK O) (E a b) + (-1 : KK O) • LinearMap.mulRight (KK O) (E a b) := by
    rw [adjointEndAction, neg_one_smul, sub_eq_add_neg]
  simp only [divPowE]
  rw [hsub, hc.add_pow, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := by simp at hm; omega
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, Module.End.natCast_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, map_nsmul, map_smul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← Nat.cast_smul_eq_nsmul (KK O), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [Nat.cast_choose (KK O) hmk]
  have h1 : ((m.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : (((k - m).factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - m)
  have h3 : ((k.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem nabla_to_delta_maps_stable [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    (lam : Fin n → ℤ) (v : V) : UZStable (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) := by
  intro u hu f hf x hx
  have hN := nabla_integral_enveloping_stable (O := O) E lam v
  have hD := delta_integral_enveloping_stable (O := O) E v
  have htop : ∀ z : V, z ∈ ⨆ mu, ⨆ (_ : True), weightSp E mu := by
    intro z
    simp only [iSup_true]
    rw [hE.2.2]
    exact Submodule.mem_top
  rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
  · rw [adjoint_divided_power_expansion, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply]
    have h1 : divPowE E a b (k - m) x ∈ NablaSub (O := O) E lam v := hN _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) x hx
    have h2 : f (divPowE E a b (k - m) x) ∈ Delta (O := O) E v := hf _ h1
    have h3 := hD _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ h2
    have h4 := intCast_smul_mem_submodule (Delta (O := O) E v) ((-1 : ℤ) ^ (k - m)) h3
    simpa using h4
  · have hR : ∀ (m : ℕ) (μ ν : Fin n → ℤ) (z : V), z ∈ weightSp E μ →
        (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) z =
          (∏ j ∈ range m, ((μ a : KK O) - ((ν a : KK O) + j))) • z := by
      intro m μ ν z hz
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          (mem_weightSpace_iff_diag_scalar.1 hz) a, ← sub_smul, map_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]
    have hw : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        (binomE (adjointEndAction E) a k f) y = ∑ ij ∈ antidiagonal k,
          (((Ring.choose (-(ν a)) ij.2 : ℤ) : KK O)) • binomE E a ij.1 (f y) := by
      intro ν y hy
      have hadx : ∀ (g : Module.End (KK O) V) (c : KK O),
          ((adjointEndAction E a a - c • (1 : Module.End (KK O) (Module.End (KK O) V))) g) y =
            (E a a - ((ν a : KK O) + c) • (1 : Module.End (KK O) V)) (g y) := by
        intro g c
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, adjointEndAction_apply,
          Module.End.mul_apply, (mem_weightSpace_iff_diag_scalar.1 hy) a, map_smul, add_smul, LinearMap.add_apply]
        abel
      have hprod : ∀ (m : ℕ) (g : Module.End (KK O) V),
          (((List.range m).map fun j : ℕ => adjointEndAction E a a - (j : KK O) •
            (1 : Module.End (KK O) (Module.End (KK O) V))).prod g) y =
          (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) (g y) := by
        intro m
        induction m with
        | zero => intro g; simp
        | succ m ih =>
          intro g
          rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
            List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton]
          simp only [Module.End.mul_apply]
          rw [ih, hadx]
      obtain ⟨G, h, hh, hfy⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop (f y))
      rw [binomE, LinearMap.smul_apply, LinearMap.smul_apply, hprod, hfy, map_sum, Finset.smul_sum]
      simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hμw := (hh μ hμ).2
      rw [hR k μ ν _ hμw, smul_smul]
      simp only [binomial_diagonal_on_weight hμw, map_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      calc ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, ((μ a : KK O) - ((ν a : KK O) + j))
          = ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, (((μ a + -(ν a) : ℤ) : KK O) - (j : KK O)) := by
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            push_cast
            ring
        _ = ((Ring.choose (μ a + -(ν a)) k : ℤ) : KK O) := inv_factorial_prod_eq_choose _ _
        _ = _ := by
            rw [Ring.add_choose_eq k (Commute.all _ _)]
            push_cast
            refine Finset.sum_congr rfl fun ij _ => ?_
            ring
    obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Module.End (KK O) V,
        S = fun j : ℕ => ((((j : ℤ).negOnePow : ℤˣ) : ℤ) : KK O) • shiftedBinomialOperator E a ((j : ℤ) - 1) j := ⟨_, rfl⟩
    have hS : ∀ (j : ℕ) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        S j y = ((Ring.choose (-(ν a)) j : ℤ) : KK O) • y := by
      intro j ν y hy
      rw [hSdef, LinearMap.smul_apply, shifted_binomial_on_weight hy, smul_smul]
      congr 1
      rw [Ring.choose_neg, Units.smul_def, smul_eq_mul, add_sub_assoc]
      push_cast
      ring
    have hop : binomE (adjointEndAction E) a k f = ∑ ij ∈ antidiagonal k, binomE E a ij.1 * f * S ij.2 := by
      apply LinearMap.ext
      intro z
      obtain ⟨F, g, hg, rfl⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop z)
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [hw ν _ (hg ν hν).2, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, hS _ _ _ (hg ν hν).2, map_smul, map_smul]
    rw [hop, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun ij _ => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    have h1 : S ij.2 x ∈ NablaSub (O := O) E lam v := by
      rw [hSdef, LinearMap.smul_apply]
      exact intCast_smul_mem_submodule _ _ (shifted_binomial_preserves_lattice hN a _ _ hx)
    have h2 : f (S ij.2 x) ∈ Delta (O := O) E v := hf _ h1
    exact hD _ (Or.inr ⟨a, ij.1, rfl⟩) _ h2

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end
