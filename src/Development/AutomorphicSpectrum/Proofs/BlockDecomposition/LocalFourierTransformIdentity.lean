import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFSupp

open ValuativeRel NNReal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem dg_mul_uni (a b : Fˣ) (x z : F) :
    Ad3.dg (a * b) b 1 * Ad3.uni x 0 z =
      Ad3.uni ((a : F) * x) 0 ((b : F) * z) * Ad3.dg (a * b) b 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg, Ad3.uni, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uni_mem_congruenceSubgroup {m : ℕ} {x z : F}
    (hx : valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (hz : valuation F z ≤ valuation F (GLnLocal.uniformizer F : F) ^ m) :
    Ad3.uni x 0 z ∈ GLnLocal.congruenceSubgroup F 3 m := by
  have h1 : valuation F (GLnLocal.uniformizer F : F) ^ m ≤ 1 :=
    pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le m
  have hxO : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr (hx.trans h1)
  have hzO : z ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr (hz.trans h1)
  have hnx : -x ∈ 𝒪[F] := neg_mem hxO
  have hnz : -z ∈ 𝒪[F] := neg_mem hzO
  have hxz : x * z ∈ 𝒪[F] := mul_mem hxO hzO
  have hinv : (((Ad3.uni x 0 z)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, -x, x * z - 0; 0, 1, -z; 0, 0, 1] := rfl
  have hval : (((Ad3.uni x 0 z) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, x, 0; 0, 1, z; 0, 0, 1] := rfl
  rw [GLnLocal.mem_congruenceSubgroup_iff]
  refine ⟨(GLnLocal.mem_integralGL_iff F 3).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [hval]
    fin_cases i <;> fin_cases j <;> simp [hxO, hzO, zero_mem, one_mem]
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp [hnx, hnz, hxz, zero_mem, one_mem]
  · rw [hval]
    fin_cases i <;> fin_cases j <;> simp [hx, hz]

theorem valuation_le_of_mem_valBall {m : ℕ} {x : F}
    (hx : x ∈ valBall F (ord ((GLnLocal.uniformizer F : F) ^ m))) :
    valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m := by
  have h0 : (GLnLocal.uniformizer F : F) ≠ 0 := fun h =>
    GLnLocal.valuation_uniformizer_ne_zero F (by rw [h, map_zero])
  obtain ⟨y, rfl⟩ := exists_mul_of_mem_valBall (pow_ne_zero m h0) hx
  rw [map_mul, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).mp y.2)

theorem psi_eq_one {ψ : AddChar F Circle} {W : GL (Fin 3) F → ℂ}
    (hW : ∀ x y z g, W (Ad3.uni x y z * g) = (ψ (x + z) : ℂ) * W g)
    {U : Set (GL (Fin 3) F)} (hU : ∀ g, ∀ u ∈ U, W (g * u) = W g) {m : ℕ}
    (hm : (GLnLocal.congruenceSubgroup F 3 m : Set (GL (Fin 3) F)) ⊆ U) (a b : Fˣ)
    {k : GL (Fin 3) F} (hk : k ∈ GLnLocal.integralGL F 3) {x z : F}
    (hx : valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (hz : valuation F z ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (h : W (Ad3.dg (a * b) b 1 * k) ≠ 0) : ψ ((a : F) * x + (b : F) * z) = 1 := by
  have hc : k⁻¹ * Ad3.uni x 0 z * k ∈ GLnLocal.congruenceSubgroup F 3 m := by
    simpa using GLnLocal.conj_mem_congruenceSubgroup F 3 (inv_mem hk)
      (uni_mem_congruenceSubgroup hx hz)
  have e1 := hU (Ad3.dg (a * b) b 1 * k) _ (hm hc)
  have e2 : Ad3.dg (a * b) b 1 * k * (k⁻¹ * Ad3.uni x 0 z * k) =
      Ad3.uni ((a : F) * x) 0 ((b : F) * z) * (Ad3.dg (a * b) b 1 * k) := by
    calc Ad3.dg (a * b) b 1 * k * (k⁻¹ * Ad3.uni x 0 z * k)
        = Ad3.dg (a * b) b 1 * Ad3.uni x 0 z * k := by group
      _ = _ := by rw [dg_mul_uni, mul_assoc]
  rw [e2, hW] at e1
  have e3 : (ψ ((a : F) * x + (b : F) * z) : ℂ) = 1 :=
    mul_right_cancel₀ h (by rw [e1, one_mul])
  exact Circle.coe_eq_one.mp e3

theorem modulus_le_of_trivial {ψ : AddChar F Circle} {y : F} (hy : y ∈ valBall F (-1))
    (hy1 : ψ y ≠ 1) {n : ℤ} (c : Fˣ) (h : ∀ x ∈ valBall F n, ψ ((c : F) * x) = 1) :
    GroundTheory.LocalField.modulus (c : F) ≤ (residueCard F : ℝ≥0) ^ (n + 1) := by
  by_contra hlt
  rw [not_le, GroundTheory.LocalField.modulus_of_ne_zero c.ne_zero,
    (zpow_right_strictMono₀ one_lt_residueCard_nnreal).lt_iff_lt] at hlt
  have h1 : (c : F)⁻¹ ∈ valBall F (-ord (c : F)) := by
    rw [← ord_inv c.ne_zero]
    exact mem_valBall_ord
  have h2 : (c : F)⁻¹ * y ∈ valBall F n :=
    valBall_antitone (by omega) (mul_mem_valBall h1 hy)
  apply hy1
  simpa [c.ne_zero] using h _ h2

end GlobalTheory.CompanionTheory.LFSupp

open GlobalTheory.CompanionTheory.LFSupp in

theorem GlobalTheory.CompanionTheory.LFSupp.sSupp : Ad3.LFS.SSupp := by
  intro F _ _ _ _ _ _ ψ hψ W hW hsm
  obtain ⟨U, hU⟩ := hsm
  obtain ⟨m, -, hm⟩ := (GLnLocal.hasBasis_nhds_one F 3).mem_iff.mp
    (U.isOpen.mem_nhds (one_mem U))
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨y, hy, hy1⟩ := hnot
  have hy' : y ∈ valBall F (-1) := by simpa using hy
  refine ⟨(((residueCard F : NNReal) ^ (ord ((GLnLocal.uniformizer F : F) ^ m) + 1) : NNReal) : ℝ),
    fun a b k hk h => ⟨?_, ?_⟩⟩
  · refine NNReal.coe_le_coe.mpr (modulus_le_of_trivial hy' hy1 a fun x hx => ?_)
    have := psi_eq_one hW (U := (U : Set _)) hU hm a b hk (valuation_le_of_mem_valBall hx)
      (z := 0) (by simp) h
    simpa using this
  · refine NNReal.coe_le_coe.mpr (modulus_le_of_trivial hy' hy1 b fun z hz => ?_)
    have := psi_eq_one hW (U := (U : Set _)) hU hm a b hk (x := 0) (by simp)
      (valuation_le_of_mem_valBall hz) h
    simpa using this
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFFour

open Ad3 Ad3.LFS Topology

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_ball_subset {ι : Type} [Fintype ι] {U : Set (ι → F)} (hU : U ∈ 𝓝 (0 : ι → F)) :
    ∃ n : ℤ, ∀ x : ι → F, (∀ i, x i ∈ valBall F n) → x ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have ht' : ∀ i, t i ∈ 𝓝 (0 : F) := fun i ↦ by simpa using ht i
  choose n hn using fun i ↦ (hasBasis_nhds_zero_valBall (K := F)).mem_iff.1 (ht' i)
  obtain ⟨N, hN⟩ := (Finset.univ.image n).exists_le
  refine ⟨N, fun x hx ↦ hsub fun i _ ↦ (hn i).2 ?_⟩
  exact valBall_antitone (hN _ (Finset.mem_image_of_mem n (Finset.mem_univ i))) (hx i)

def bx (ι : Type) (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) : Set (ι → F) :=
  Set.pi Set.univ fun _ ↦ (valBall F n : Set F)

theorem mem_bx {ι : Type} {n : ℤ} {x : ι → F} : x ∈ bx ι F n ↔ ∀ i, x i ∈ valBall F n := by
  simp [bx, Set.mem_univ_pi]

theorem isOpen_bx {ι : Type} [Fintype ι] (n : ℤ) : IsOpen (bx ι F n) :=
  isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n

theorem exists_invariant {ι : Type} [Fintype ι] {Φ : (ι → F) → ℂ} (hlc : IsLocallyConstant Φ)
    (hcs : HasCompactSupport Φ) :
    ∃ N M : ℤ, (∀ x h, (∀ i, h i ∈ valBall F N) → Φ (x + h) = Φ x) ∧
      ∀ x, Φ x ≠ 0 → ∀ i, x i ∈ valBall F M := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, tsupport Φ ⊆ bx ι F (-(m : ℤ)) := by
    refine hcs.isCompact.elim_directed_cover (fun m : ℕ ↦ bx ι F (-(m : ℤ)))
      (fun m ↦ isOpen_bx _) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      choose a ha using fun i ↦ exists_mem_valBall_neg_nat (x i)
      refine ⟨Finset.univ.sup a, mem_bx.2 fun i ↦ valBall_antitone ?_ (ha i)⟩
      have : a i ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ i)
      omega
    · exact Monotone.directed_le fun a b hab x hx ↦
        mem_bx.2 fun i ↦ valBall_antitone (by omega) (mem_bx.1 hx i)
  have hloc : ∀ x : ι → F, ∃ n : ℤ, ∀ h, (∀ i, h i ∈ valBall F n) → Φ (x + h) = Φ x := by
    intro x
    have ho : IsOpen {h : ι → F | Φ (x + h) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, hn⟩ := exists_ball_subset (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh ↦ hn h hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x ↦ {z : ι → F | z - x ∈ bx ι F (n x)})
    (fun x _ ↦ ((isOpen_bx _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp [mem_bx, zero_mem]))
  obtain ⟨N₀, hN⟩ := (t.image n).exists_le
  have hval : ∀ y ∈ tsupport Φ, ∀ h, (∀ i, h i ∈ valBall F N₀) → Φ (y + h) = Φ y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hyx' := mem_bx.1 hyx
    have hN' : ∀ i, h i ∈ valBall F (n x) := fun i ↦
      valBall_antitone (hN _ (Finset.mem_image_of_mem n hxt)) (hh i)
    have e1 : Φ y = Φ x := by
      have := hn x (y - x) hyx'
      rwa [add_sub_cancel] at this
    have e2 : Φ (y + h) = Φ x := by
      have := hn x (y + h - x) (fun i ↦ by
        rw [show (y + h - x) i = (y - x) i + h i by simp; abel]
        exact add_mem (hyx' i) (hN' i))
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N₀, -(m : ℤ), fun y h hh ↦ ?_, fun x hx ↦ mem_bx.1 (hm (subset_tsupport Φ hx))⟩
  by_cases hy : y ∈ tsupport Φ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Φ
  · have := hval (y + h) hyh (-h) (fun i ↦ by simpa using neg_mem (hh i))
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

def mh : (Fin 2 × Fin 3 → F) ≃ₜ Matrix (Fin 2) (Fin 3) F where
  toFun f := Matrix.of fun i j ↦ f (i, j)
  invFun X p := X p.1 p.2
  left_inv f := rfl
  right_inv X := rfl
  continuous_toFun := continuous_matrix fun i j ↦ continuous_apply (i, j)
  continuous_invFun := continuous_pi fun p ↦ continuous_id.matrix_elem p.1 p.2

theorem exists_invariant_matrix {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ N M : ℤ, (∀ X Y : Matrix (Fin 2) (Fin 3) F, (∀ a b, Y a b ∈ valBall F N) → Φ (X + Y) = Φ X) ∧
      ∀ X, Φ X ≠ 0 → ∀ a b, X a b ∈ valBall F M := by
  obtain ⟨N, M, h1, h2⟩ := exists_invariant (Φ := Φ ∘ (mh (F := F)))
    (hlc.comp_continuous (mh (F := F)).continuous) (hcs.comp_homeomorph (mh (F := F)))
  refine ⟨N, M, fun X Y hY ↦ ?_, fun X hX a b ↦ ?_⟩
  · exact h1 (mh.symm X) (mh.symm Y) (fun p ↦ hY p.1 p.2)
  · exact h2 (mh.symm X) (by simpa using hX) (a, b)

theorem modulus_le_zpow_of_mem {M : ℤ} {x : F} (hx : x ∈ valBall F M) :
    (GroundTheory.LocalField.modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (-M) := by
  have hq : (1 : ℝ) ≤ residueCard F := by exact_mod_cast one_lt_residueCard.le
  by_cases h0 : x = 0
  · subst h0
    simp only [modulus_zero, NNReal.coe_zero]
    positivity
  rw [modulus_of_ne_zero h0, NNReal.coe_zpow, NNReal.coe_natCast]
  exact zpow_le_zpow_right₀ hq (by have := (mem_valBall_iff_le_ord h0).mp hx; omega)

theorem column_three_add (k : Matrix (Fin 2) (Fin 2) F) (y e : Fin 2 → F) :
    col3 k (y + e) = col3 k y + col3 0 e := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [col3]

theorem three_column_matrix_last (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) (a : Fin 2) :
    col3 k y a 2 = y a := by
  fin_cases a <;> simp [col3]

theorem three_column_matrix_left (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) (a b : Fin 2) :
    col3 k y a b.castSucc = k a b := by
  fin_cases a <;> fin_cases b <;> simp [col3]

theorem three_column_zero_mem_ball {N : ℤ} (e : Fin 2 → F) (he : ∀ a, e a ∈ valBall F N) (a : Fin 2) (b : Fin 3) :
    col3 (0 : Matrix (Fin 2) (Fin 2) F) e a b ∈ valBall F N := by
  have h0 : (0 : F) ∈ valBall F N := zero_mem _
  have h1 := he 0
  have h2 := he 1
  fin_cases a <;> fin_cases b <;> simpa [col3] using (by assumption)

variable [MeasurableSpace F] [BorelSpace F]

theorem pft_eq_mul (ψ : AddChar F Circle) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} {N : ℤ}
    (hinv : ∀ X Y : Matrix (Fin 2) (Fin 3) F, (∀ a b, Y a b ∈ valBall F N) → Φ (X + Y) = Φ X)
    (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) (j : Fin 2) {c : F} (hc : c ∈ valBall F N) :
    pft ψ Φ k ξ = (ψ (-(ξ j * c)) : ℂ) * pft ψ Φ k ξ := by
  have hv : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  have hmem : ∀ a b, col3 (0 : Matrix (Fin 2) (Fin 2) F) (Pi.single j c) a b ∈ valBall F N :=
    three_column_zero_mem_ball _ fun a ↦ by
      rw [Pi.single_apply]
      split_ifs
      · exact hc
      · exact zero_mem _
  have h := integral_add_right_eq_self (μ := vol2 ψ)
    (fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) (Pi.single j c)
  unfold pft
  rw [← integral_const_mul, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  have e1 : ∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i = ∑ i, ξ i * y i + ξ j * c := by
    simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
  show Φ (col3 k (y + (Pi.single j c : Fin 2 → F))) *
    (ψ (-(∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i)) : ℂ) = _
  rw [column_three_add, hinv _ _ hmem, e1, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem norm_pft_le (ψ : AddChar F Circle) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} {M : ℤ} {B : ℝ}
    (hB : ∀ X, ‖Φ X‖ ≤ B) (hs : ∀ X, Φ X ≠ 0 → ∀ a b, X a b ∈ valBall F M)
    (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) :
    ‖pft ψ Φ k ξ‖ ≤ (vol2 ψ).real (bx (Fin 2) F M) * B := by
  have hv : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  have hS : MeasurableSet (bx (Fin 2) F M) :=
    MeasurableSet.univ_pi fun _ ↦ (isClosed_valBall M).measurableSet
  have hfin : vol2 ψ (bx (Fin 2) F M) ≠ ⊤ :=
    (IsCompact.measure_lt_top (isCompact_univ_pi fun _ ↦ isCompact_valBall M)).ne
  have hint : Integrable ((bx (Fin 2) F M).indicator fun _ ↦ B) (vol2 ψ) :=
    (integrable_indicator_iff hS).2 (integrableOn_const hfin)
  have := norm_integral_le_of_norm_le (μ := vol2 ψ)
    (f := fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) hint
    (Filter.Eventually.of_forall fun y ↦ ?_)
  · rw [integral_indicator_const _ hS, smul_eq_mul] at this
    exact this
  · rw [norm_mul, Circle.norm_coe, mul_one]
    by_cases hy : y ∈ bx (Fin 2) F M
    · rw [Set.indicator_of_mem hy]
      exact hB _
    · rw [Set.indicator_of_notMem hy]
      by_cases h0 : Φ (col3 k y) = 0
      · simp [h0]
      · exact absurd (mem_bx.2 fun a ↦ by
          simpa [three_column_matrix_last] using hs _ h0 a 2) hy

end GlobalTheory.CompanionTheory.LFFour

open GlobalTheory.CompanionTheory.LFFour in

theorem GlobalTheory.CompanionTheory.LFFour.gFour : Ad3.LFS.GFour := by
  intro F _ _ _ _ _ _ ψ hψ Φ hΦ
  obtain ⟨N, M, hinv, hsupp⟩ := exists_invariant_matrix hΦ.1 hΦ.2
  obtain ⟨B, hB⟩ := hΦ.2.exists_bound_of_continuous hΦ.1.continuous
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨y, hy, hy1⟩ := hnot
  have hy' : y ∈ valBall F (-1) := by simpa using hy
  refine ⟨(Ad3.LFS.vol2 ψ).real (bx (Fin 2) F M) * B,
    max ((residueCard F : ℝ) ^ (-M))
      (((residueCard F : NNReal) ^ (N + 1) : NNReal) : ℝ),
    fun k ξ ↦ ⟨norm_pft_le ψ hB hsupp k ξ, fun hne ↦ ⟨fun i j ↦ ?_, fun j ↦ ?_⟩⟩⟩
  · have hex : ∃ y, Φ (Ad3.LFS.col3 k y) ≠ 0 := by
      by_contra hno
      push_neg at hno
      exact hne (by simp [Ad3.LFS.pft, hno])
    obtain ⟨z, hz⟩ := hex
    have := hsupp _ hz i j.castSucc
    rw [three_column_matrix_left] at this
    exact (modulus_le_zpow_of_mem this).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    by_cases hξ : ξ j = 0
    · simp [hξ]
      positivity
    · refine NNReal.coe_le_coe.mpr
        (GlobalTheory.CompanionTheory.LFSupp.modulus_le_of_trivial hy' hy1 (Units.mk0 (ξ j) hξ) fun x hx ↦ ?_)
      have e := pft_eq_mul ψ hinv k ξ j (neg_mem hx)
      have e2 : (ψ (-(ξ j * -x)) : ℂ) = 1 :=
        mul_right_cancel₀ hne (by rw [← e, one_mul])
      have e3 := Circle.coe_eq_one.mp e2
      simpa using e3
end
