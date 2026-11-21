import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import BuildAid.ForwardExisting

section
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TensorComplete

section Elementary

variable {A : Type} [CommRing A] (π : A)

theorem smodEq_span_iff {M : Type} [AddCommGroup M] [Module A M] (n : ℕ) (x y : M) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule A M)] ↔ ∃ z : M, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem isAdicComplete_span_iff {M : Type} [AddCommGroup M] [Module A M] :
    IsAdicComplete (Ideal.span {π}) M ↔
      (∀ x : M, (∀ n : ℕ, ∃ z : M, π ^ n • z = x) → x = 0) ∧
      ∀ u : ℕ → M, (∀ n : ℕ, ∃ z : M, π ^ n • z = u n - u (n + 1)) →
        ∃ L : M, ∀ n : ℕ, ∃ z : M, π ^ n • z = u n - L := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun u hu => ?_⟩
    · refine h.toIsHausdorff.haus x fun n => ?_
      rw [smodEq_span_iff, sub_zero]
      exact hx n
    · have hc : ∀ {m n : ℕ}, m ≤ n →
          u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule A M)] := by
        intro m n hmn
        rw [smodEq_span_iff]
        induction n, hmn using Nat.le_induction with
        | base => exact ⟨0, by simp⟩
        | succ k hk ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨w, hw⟩ := hu k
          refine ⟨z + π ^ (k - m) • w, ?_⟩
          rw [smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]
          abel
      obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec hc
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).1 (hL n)⟩
  · rintro ⟨h1, h2⟩
    haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by
      simpa using (smodEq_span_iff π n _ _).1 (hx n)⟩
    haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by
      obtain ⟨L, hL⟩ := h2 u fun n => (smodEq_span_iff π n _ _).1 (hu (Nat.le_succ n))
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).2 (hL n)⟩⟩
    exact ⟨⟩

variable {π}

theorem isAdicComplete_of_linearEquiv {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · have : e.symm x = 0 := h1 _ fun n => by
      obtain ⟨z, hz⟩ := hx n
      exact ⟨e.symm z, by rw [← map_smul, hz]⟩
    simpa using this
  · obtain ⟨L, hL⟩ := h2 (fun n => e.symm (u n)) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨e.symm z, by rw [← map_smul, hz, map_sub]⟩
    refine ⟨e L, fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    exact ⟨e z, by rw [← map_smul, hz, map_sub, LinearEquiv.apply_symm_apply]⟩

theorem isAdicComplete_prod {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : IsAdicComplete (Ideal.span {π}) M)
    (h' : IsAdicComplete (Ideal.span {π}) M') : IsAdicComplete (Ideal.span {π}) (M × M') := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  obtain ⟨h1', h2'⟩ := (isAdicComplete_span_iff π).1 h'
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · refine Prod.ext (h1 _ fun n => ?_) (h1' _ fun n => ?_)
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.1, by rw [← hz]; rfl⟩
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.2, by rw [← hz]; rfl⟩
  · obtain ⟨L, hL⟩ := h2 (fun n => (u n).1) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.1, by simpa using congrArg Prod.fst hz⟩
    obtain ⟨L', hL'⟩ := h2' (fun n => (u n).2) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.2, by simpa using congrArg Prod.snd hz⟩
    refine ⟨(L, L'), fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    obtain ⟨z', hz'⟩ := hL' n
    exact ⟨(z, z'), Prod.ext hz hz'⟩

theorem isAdicComplete_fin_pi {M : Type} [AddCommGroup M] [Module A M]
    (h : IsAdicComplete (Ideal.span {π}) M) (n : ℕ) :
    IsAdicComplete (Ideal.span {π}) (Fin n → M) := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · funext i
    refine h1 _ fun k => ?_
    obtain ⟨z, hz⟩ := hx k
    exact ⟨z i, by rw [← hz]; rfl⟩
  · choose z hz using hu
    have key : ∀ i : Fin n, ∃ L : M, ∀ k : ℕ, ∃ w : M, π ^ k • w = u k i - L := fun i =>
      h2 (fun k => u k i) fun k => ⟨z k i, by simpa using congrFun (hz k) i⟩
    choose L hL using key
    refine ⟨L, fun k => ?_⟩
    choose w hw using fun i => hL i k
    exact ⟨w, funext hw⟩

theorem isAdicComplete_of_pow_smul_eq_zero {M : Type} [AddCommGroup M] [Module A M] (E : ℕ)
    (h : ∀ x : M, π ^ E • x = 0) : IsAdicComplete (Ideal.span {π}) M := by
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · obtain ⟨z, rfl⟩ := hx E
    exact h z
  · have tel : ∀ n k : ℕ, ∃ z : M, π ^ n • z = u n - u (n + k) := by
      intro n k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := ih
        obtain ⟨w, hw⟩ := hu (n + k)
        refine ⟨z + π ^ k • w, ?_⟩
        rw [smul_add, smul_smul, ← pow_add, hz, hw, ← add_assoc]
        abel
    refine ⟨u E, fun n => ?_⟩
    obtain ⟨z, hz⟩ := tel n E
    obtain ⟨w, hw⟩ := tel E n
    rw [h w, add_comm E n] at hw
    refine ⟨z, ?_⟩
    rw [hz, ← sub_eq_zero.1 hw.symm]

end Elementary

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]

theorem irreducible_dvd_of_not_isUnit {q r : R} (hq : Irreducible q) (hr : ¬IsUnit r) : q ∣ r := by
  have hmax : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq
  have heq : Ideal.span {q} = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  rw [← Ideal.mem_span_singleton, heq]
  exact (IsLocalRing.mem_maximalIdeal r).2 hr

theorem exists_pow_smul_directSum_eq_zero {ι : Type} [Fintype ι] (q : ι → R)
    (hq : ∀ i, Irreducible (q i)) (e : ι → ℕ) {r : R} (hr : ¬IsUnit r) :
    ∃ E : ℕ, ∀ x : DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i}), r ^ E • x = 0 := by
  classical
  refine ⟨∑ i, e i, fun x => ?_⟩
  refine DFinsupp.ext fun i => ?_
  have hmem : r ^ (∑ i, e i) ∈ Submodule.span R {q i ^ e i} := by
    rw [Submodule.mem_span_singleton]
    have h1 : q i ^ e i ∣ r ^ (∑ i, e i) :=
      (pow_dvd_pow_of_dvd (irreducible_dvd_of_not_isUnit (hq i) hr) (e i)).trans
        (pow_dvd_pow r (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
  change r ^ (∑ i, e i) • x i = 0
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simpa [smul_eq_mul, mul_comm] using Submodule.smul_mem _ y hmem

theorem pow_natCast_smul_tensor_eq_zero {O T : Type} [CommRing O] [Algebra R O] [AddCommGroup T]
    [Module R T] (p E : ℕ) (h : ∀ x : T, (p : R) ^ E • x = 0) (t : O ⊗[R] T) :
    (p : O) ^ E • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul o x =>
    have h1 : (p : O) ^ E * o = (p : R) ^ E • o := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [TensorProduct.smul_tmul', smul_eq_mul, h1, TensorProduct.smul_tmul, h x,
      TensorProduct.tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

end Tensor

theorem isAdicComplete_tensor : ∀ (p : ℕ) [Fact p.Prime] (R O : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] [CommRing O] [Algebra R O]
    [IsAdicComplete (Ideal.span {(p : O)}) O],
    (p : R) ≠ 0 → ¬IsUnit (p : R) →
    ∀ (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] N) := by
  intro p _ R O _ _ _ _ _ _ _ hp1 hp2 N _ _ _
  obtain ⟨n, ι, _, q, hq, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := R) (M := N)
  obtain ⟨E, hE⟩ := exists_pow_smul_directSum_eq_zero q hq e hp2
  have hfree : IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] (Fin n →₀ R)) :=
    isAdicComplete_of_linearEquiv
      ((Finsupp.linearEquivFunOnFinite O O (Fin n)).symm.trans
        (TensorProduct.finsuppScalarRight R O O (Fin n)).symm)
      (isAdicComplete_fin_pi inferInstance n)
  have htors : IsAdicComplete (Ideal.span {(p : O)})
      (O ⊗[R] DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i})) :=
    isAdicComplete_of_pow_smul_eq_zero E (pow_natCast_smul_tensor_eq_zero p E hE)
  exact isAdicComplete_of_linearEquiv
    ((TensorProduct.prodRight R O O _ _).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O O) f).symm)
    (isAdicComplete_prod hfree htors)

end GlobalTheory.CompanionTheory.TensorComplete
end
end

section
open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorCompleteFinite

open GlobalTheory.CompanionTheory.TensorComplete

theorem isAdicComplete_of_linearEquiv_univ {A : Type} [CommRing A] {π : A} {M : Type} {M' : Type 1}
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  have hM : ∀ (n : ℕ) (x : M), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) →
      e x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M).map (e : M →ₗ[A] M') ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  have hM' : ∀ (n : ℕ) (x : M'), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') →
      e.symm x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M').map (e.symm : M' →ₗ[A] M) ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e.symm x = 0 := by
      refine h.toIsHausdorff.haus' (e.symm x) (fun n => ?_)
      rw [SModEq.sub_mem, sub_zero]
      have hx' := (SModEq.sub_mem).mp (hx n)
      rw [sub_zero] at hx'
      exact hM' n x hx'
    simpa using congrArg e h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e.symm (f n)) (fun {m n} hmn => by
      rw [SModEq.sub_mem, ← map_sub]
      exact hM' m _ ((SModEq.sub_mem).mp (hf hmn)))
    refine ⟨e L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have h2 := hM n _ ((SModEq.sub_mem).mp (hL n))
    rwa [map_sub, LinearEquiv.apply_symm_apply] at h2

theorem isAdicComplete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) →
    ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
      (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L],
      IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  intro W _ _ _ l hl A _ _ hA L _ _ _
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hl.ne_zero Nat.cast_zero
  obtain ⟨p, hpmem, hpu⟩ : ∃ p ∈ l.primeFactorsList, ¬IsUnit (p : W) := by
    by_contra hcon
    push_neg at hcon
    apply hl.1
    rw [← Nat.prod_primeFactorsList hl0, Nat.cast_list_prod]
    refine List.prod_isUnit (fun m hm => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hcon q hq
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hpmem
  obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactorsList hpmem
  have hmu : IsUnit (m : W) := by
    have h := hl.isUnit_or_isUnit (show (l : W) = (p : W) * (m : W) by rw [hm, Nat.cast_mul])
    exact h.resolve_left hpu
  have hmA : IsUnit (m : A) := by
    have h := hmu.map (algebraMap W A)
    rwa [map_natCast] at h
  have hI : Ideal.span {(l : A)} = Ideal.span {(p : A)} := by
    rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit hmA]
  have hp0 : (p : W) ≠ 0 := by
    intro h
    apply hl.ne_zero
    rw [hm, Nat.cast_mul, h, zero_mul]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hA' : IsAdicComplete (Ideal.span {(p : A)}) A := by
    rw [← hI]
    exact hA
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' W L
  have hN := isAdicComplete_tensor p W A hp0 hpu ((Fin n → W) ⧸ LinearMap.ker f)
  rw [hI]
  exact isAdicComplete_of_linearEquiv_univ
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (f.quotKerEquivOfSurjective hf)) hN

end GlobalTheory.CompanionTheory.TensorCompleteFinite
end

section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_complete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A] (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L], IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite
end

section
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerExt

section
variable {W : Type} [CommRing W] (l : ℕ) {A : Type} [CommRing A] [Algebra W A]
  {M : Type*} [AddCommGroup M] [Module W M]

theorem pow_smul_tmul (n : ℕ) (a : A) (m : M) :
    ((l : A) ^ n) • (a ⊗ₜ[W] m) = a ⊗ₜ[W] (((l : W) ^ n) • m) := by
  have h : ((l : W) ^ n) • a = (l : A) ^ n * a := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [← TensorProduct.smul_tmul, h, TensorProduct.smul_tmul', smul_eq_mul]

theorem pow_smul_eq_zero (n : ℕ) (h : ∀ x : M, ((l : W) ^ n) • x = 0) (t : A ⊗[W] M) :
    ((l : A) ^ n) • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [pow_smul_tmul, h, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem lTensor_pow_smul (n : ℕ) (v : A ⊗[W] M) :
    LinearMap.lTensor A (((l : W) ^ n) • (LinearMap.id : M →ₗ[W] M)) v = ((l : A) ^ n) • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [pow_smul_tmul, LinearMap.lTensor_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

theorem mem_pow_smul_top {N : Type*} [AddCommGroup N] [Module A N] (n : ℕ) (v : N) :
    v ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A N) ↔ ∃ u : N, v = ((l : A) ^ n) • u := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, Submodule.mem_top, rfl⟩
end

section
variable {W : Type} [CommRing W] (l : ℕ) (S : Sys.{1} W) (A : Type) [CommRing A] [Algebra W A]

theorem r_baseChange_pr (n : ℕ) (w : A ⊗[W] S.lim) :
    (S.r n).baseChange A ((pr S (n + 1)).baseChange A w) = (pr S n).baseChange A w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have hx : S.r n (x.1 (n + 1)) = x.1 n := x.2 n
    simp only [LinearMap.baseChange_tmul]
    change a ⊗ₜ[W] S.r n (x.1 (n + 1)) = a ⊗ₜ[W] x.1 n
    rw [hx]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_eq_pow_smul [Module.Flat W A] (n : ℕ)
    (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : (pr S n).baseChange A w = 0) :
    ∃ v : A ⊗[W] S.lim, w = ((l : A) ^ n) • v := by
  have hex : Function.Exact (((l : W) ^ n) • (LinearMap.id : S.lim →ₗ[W] S.lim)) (pr S n) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hker x hx
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      change (pr S n) (((l : W) ^ n) • y) = 0
      rw [map_smul]
      exact hkill _
  have hw' : (LinearMap.lTensor A (pr S n)) w = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]
    exact hw
  obtain ⟨v, rfl⟩ := (Module.Flat.lTensor_exact A hex w).1 hw'
  exact ⟨v, lTensor_pow_smul l n v⟩

theorem baseChange_pr_pow_smul (n : ℕ) (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (u : A ⊗[W] S.lim) : (pr S n).baseChange A (((l : A) ^ n) • u) = 0 := by
  rw [map_smul]
  exact pow_smul_eq_zero l n hkill _

theorem exists_baseChange_pr_eq (n c : ℕ)
    (hcok : ∀ (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) (t : A ⊗[W] S.M n) :
    ∃ w : A ⊗[W] S.lim, (pr S n).baseChange A w = ((l : A) ^ c) • t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨y, hy⟩ := hcok m
    refine ⟨a ⊗ₜ[W] y, ?_⟩
    rw [pow_smul_tmul, ← hy, LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨w₁, h₁⟩ := hx
    obtain ⟨w₂, h₂⟩ := hy
    exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, smul_add]⟩

theorem eq_zero_of_baseChange_pr [Module.Flat W A]
    [IsHausdorff (Ideal.span {(l : A)}) (A ⊗[W] S.lim)]
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : ∀ n, (pr S n).baseChange A w = 0) : w = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance w fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top]
  exact exists_eq_pow_smul l S A n (hkill n) (hker n) w (hw n)

theorem exists_lift [Module.Flat W A]
    [IsPrecomplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim)] (c : ℕ)
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (hcok : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x)
    (z : ∀ n, A ⊗[W] S.M n) (hz : ∀ n, (S.r n).baseChange A (z (n + 1)) = z n) :
    ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w = ((l : A) ^ c) • z n := by
  choose f hf using fun n => exists_baseChange_pr_eq l S A n c (hcok n) (z n)
  have hstep : ∀ n, f n ≡ f (n + 1) [SMOD ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro n
    rw [SModEq.sub_mem, mem_pow_smul_top]
    refine exists_eq_pow_smul l S A n (hkill n) (hker n) _ ?_
    rw [map_sub, ← r_baseChange_pr S A n (f (n + 1)), hf (n + 1), map_smul, hz, hf n, sub_self]
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {(l : A)}) ^ m • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem] at *
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) ((SModEq.sub_mem).1 (hstep n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance hmono
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, mem_pow_smul_top] at h
  obtain ⟨u, hu⟩ := h
  have h0 : (pr S n).baseChange A (f n - L) = 0 := by
    rw [hu]
    exact baseChange_pr_pow_smul l S A n (hkill n) u
  rw [map_sub, sub_eq_zero, hf n] at h0
  exact h0.symm

end

theorem limit_extension_upTo : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (S : Sys.{1} W) (c : ℕ), Module.Finite W S.lim → (∀ n (x : S.M n), ((l : W) ^ n) • x = 0) → (∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y) → (∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A], (∀ w : A ⊗[W] S.lim, (∀ n, (pr S n).baseChange A w = 0) → w = 0) ∧ ∃ α : (tens A S).lim →ₗ[A] A ⊗[W] S.lim, ∀ z n, (pr S n).baseChange A (α z) = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := by
  intro W _ _ _ l hl S c hfin hkill hker hcok A _ _ _ _
  haveI hcompl : IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim) :=
    GlobalTheory.T.adic_complete_tensor_finite W l hl A S.lim
  have hinj := eq_zero_of_baseChange_pr l S A hkill hker
  refine ⟨hinj, ?_⟩
  have hlift : ∀ z : (tens A S).lim, ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w =
      ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := fun z =>
    exists_lift l S A c hkill hker hcok (fun n => z.1 n) fun n => z.2 n
  choose g hg using hlift
  refine ⟨{ toFun := g, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hg⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, map_add, hg, hg, hg]
    exact sub_eq_zero.2 (smul_add ((l : A) ^ c) (x.1 n : A ⊗[W] S.M n) (y.1 n : A ⊗[W] S.M n))
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, RingHom.id_apply, map_smul, hg, hg]
    exact sub_eq_zero.2 (smul_comm ((l : A) ^ c) a (x.1 n : A ⊗[W] S.M n))

end GlobalTheory.CompanionTheory.TowerExt
end

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_base_change_limit_system : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (S : Sys.{1} W) (c : ℕ), Module.Finite W S.lim → (∀ n (x : S.M n), ((l : W) ^ n) • x = 0) → (∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y) → (∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A], (∀ w : A ⊗[W] S.lim, (∀ n, (pr S n).baseChange A w = 0) → w = 0) ∧ ∃ α : (tens A S).lim →ₗ[A] A ⊗[W] S.lim, ∀ z n, (pr S n).baseChange A (α z) = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TowerExt.limit_extension_upTo
end
