import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagLatticesNearUnderStabiliser
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairIdealKillsDiscriminantModulesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram

section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ II N.F N.F' ⊔ Submodule.span K {N.F.z} ⊔ N.Ist, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 := by
  first | exact @GlobalTheory.DegCnt.PosJ.main | exact GlobalTheory.DegCnt.PosJ.main | (intros; apply GlobalTheory.DegCnt.PosJ.main <;> assumption)
end

section
section
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.PosIso

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

theorem exists_section (M : Submodule (𝓞 K) V) (hM : M.FG) (φ : V →ₗ[K] K) (h0 : ∃ y ∈ M, φ y ≠ 0) :
    ∃ v ∈ Submodule.span K (M : Set V), φ v = 1 ∧ ∀ y ∈ M, φ y • v ∈ M := by
  let J : Submodule (𝓞 K) K := M.map (φ.restrictScalars (𝓞 K))
  have hJ : J.FG := hM.map _
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hI : I ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := h0
    intro h
    have : φ y ∈ I := ⟨y, hy, rfl⟩
    rw [h] at this
    exact hy0 (by simpa using this)
  have h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  rw [FractionalIdeal.coe_mul] at h1
  have key : ∀ w ∈ (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ v ∈ Submodule.span K (M : Set V), φ v = w ∧ ∀ y ∈ M, φ y • v ∈ M := by
    intro w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · rintro _ ⟨y0, hy0, rfl⟩ β hβ
      refine ⟨β • y0, Submodule.smul_mem _ _ (Submodule.subset_span hy0), by simp [mul_comm], fun y hy => ?_⟩
      have hm : φ y * β ∈ (I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :=
        FractionalIdeal.mul_mem_mul (show φ y ∈ I from ⟨y, hy, rfl⟩) hβ
      rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨o, ho⟩ := hm
      rw [smul_smul, ← ho, algebraMap_smul]
      exact M.smul_mem _ hy0
    · rintro _ _ ⟨v, hv, rfl, h⟩ ⟨v', hv', rfl, h'⟩
      exact ⟨v + v', add_mem hv hv', by simp, fun y hy => by rw [smul_add]; exact add_mem (h y hy) (h' y hy)⟩
  exact key 1 h1

omit [NumberField K] in

theorem det_smul_mem (H : HermSpace K V) (Λ : Submodule (𝓞 K) V) {j : ℕ} (x x' : Fin j → V)
    (hx : ∀ a, x a ∈ Λ) (hG : ∀ a b, H.B (x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) (p : Fin j → K)
    (hp : ∀ b, H.B (∑ a, p a • x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) :
    (Matrix.of fun a b => H.B (x a) (x' b)).det • (∑ a, p a • x a) ∈ Λ := by
  choose G0 hG0 using fun a b => Submodule.mem_one.1 (hG a b)
  choose η hη using fun b => Submodule.mem_one.1 (hp b)
  set G : Matrix (Fin j) (Fin j) K := Matrix.of fun a b => H.B (x a) (x' b) with hGdef
  have hGm : G = (algebraMap (𝓞 K) K).mapMatrix (Matrix.of G0) := by
    ext a b; simp [hGdef, ← hG0]
  have h1 : Matrix.vecMul p G = fun b => algebraMap (𝓞 K) K (η b) := by
    funext b
    rw [hη]
    simp [Matrix.vecMul, dotProduct, hGdef, map_sum]
  have h2 : G.det • p = Matrix.vecMul (Matrix.vecMul p G) G.adjugate := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  have h3 : G.det * p a = algebraMap (𝓞 K) K (∑ b, η b * (Matrix.of G0).adjugate b a) := by
    have := congrFun h2 a
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [this, h1, hGm, ← RingHom.map_adjugate]
    simp [Matrix.vecMul, dotProduct, map_sum]
  rw [smul_smul, h3, algebraMap_smul]
  exact Λ.smul_mem _ (hx a)

omit [StarRing K] in
theorem ipow_add (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 (m + n) = ipow 𝔡 m * ipow 𝔡 n := by
  unfold ipow
  rw [zpow_add₀ (by simpa using h), FractionalIdeal.coe_mul]

omit [StarRing K] in
theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  unfold ipow; simp

omit [StarRing K] in
theorem ipow_sum (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ipow 𝔡 (∑ i ∈ s, f i) = ∏ i ∈ s, ipow 𝔡 (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ipow_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ipow_add _ h, ih]

theorem star_mem_one {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact Submodule.mem_one.2 ⟨⟨_, this⟩, rfl⟩

theorem star_mem_ipow_nat (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
  induction n with
  | zero => intro x hx; simp only [Nat.cast_zero, ipow_zero] at hx ⊢; exact star_mem_one hx
  | succ n ih =>
    intro x hx
    rw [Nat.cast_succ, ipow_add _ h] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [star_mul']
      refine Submodule.mul_mem_mul (ih a ha) ?_
      simp only [ipow, zpow_one] at hb ⊢
      obtain ⟨o, ho, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      obtain ⟨y, hy, hy'⟩ := hs o ho
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, hy'⟩
    · intro a b ha hb; rw [star_add]; exact add_mem ha hb

theorem star_mem_ipow_neg (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ ipow 𝔡 (-(n : ℤ)), star x ∈ ipow 𝔡 (-(n : ℤ)) := by
  have hne : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (n : ℤ)) ≠ 0 := zpow_ne_zero _ (by simpa using h)
  have key : ∀ x : K, x ∈ ipow 𝔡 (-(n : ℤ)) ↔ ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x
    unfold ipow
    rw [zpow_neg, FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne]
    simp only [FractionalIdeal.mem_coe, ← FractionalIdeal.coe_one (S := (𝓞 K)⁰)]
  intro x hx
  rw [key] at hx ⊢
  intro y hy
  have := star_mem_one (hx _ (star_mem_ipow_nat 𝔡 h hs n y hy))
  simpa using this

omit [StarRing K] in
theorem prod_le_of_forall {ι : Type} [Fintype ι] (A : ι → Submodule (𝓞 K) K) (J : Submodule (𝓞 K) K)
    (h : ∀ f : ι → K, (∀ i, f i ∈ A i) → ∏ i, f i ∈ J) : ∏ i, A i ≤ J := by
  have : ∏ i, A i = ∏ i, Submodule.span (𝓞 K) (A i : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (Set.mem_fintype_prod _ _).1 hy
  exact h f hf

variable {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_coords (F : FlagD H r) {j : ℕ} (hj : j ≤ r + 1) {n : ℕ} (hn : n ≤ j) {y : V} (hy : y ∈ F.Xa n) :
    ∃ p : Fin j → K, (∀ b : Fin j, n ≤ b.val → p b = 0) ∧ y = ∑ b, p b • F.e (Fin.castLE hj b) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have hb' : b.val < n := hb
    refine ⟨Pi.single ⟨b.val, by omega⟩ 1, fun c hc => Pi.single_eq_of_ne ?_ _, ?_⟩
    · intro h; rw [h] at hc; simp at hc; omega
    · rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
      · simp only [Pi.single_eq_same, one_smul]; rfl
      · intro c _ hc; rw [Pi.single_eq_of_ne hc, zero_smul]
      · simp
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨p, hp, rfl⟩ := h
    obtain ⟨p', hp', rfl⟩ := h'
    exact ⟨p + p', fun b hb => by simp [hp b hb, hp' b hb], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a y _ h =>
    obtain ⟨p, hp, rfl⟩ := h
    exact ⟨a • p, fun b hb => by simp [hp b hb], by simp [Finset.smul_sum, smul_smul]⟩

omit [NumberField K] in
theorem exists_tri (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (aa : Fin r → Submodule (𝓞 K) K) (hF : IsFrame F Λ aa)
    {j : ℕ} (hj : j ≤ r) (s : Fin j → K) (hs : ∀ a, s a ∈ aa (Fin.castLE hj a)) :
    ∃ A : Matrix (Fin j) (Fin j) K, A.det = ∏ a, s a ∧
      ∀ a, ∑ c, A a c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) ∈ Λ := by
  have h : ∀ a : Fin j, ∃ p : Fin j → K, (∀ b : Fin j, a.val ≤ b.val → p b = 0) ∧
      s a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) -
        ∑ b, p b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) ∈ Λ := by
    intro a
    have h1 := hs a
    rw [← hF.1] at h1
    obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 h1
    obtain ⟨p, hp, rfl⟩ := Xa_coords F (hj.trans (Nat.le_succ r)) (n := a.val) a.isLt.le hξ
    refine ⟨p, hp, ?_⟩
    have he' : l + ∑ b, p b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) =
      s a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) := he
    rw [← he']; simpa using hl
  choose p hp hΛ using h
  refine ⟨Matrix.diagonal s - Matrix.of p, ?_, fun a => ?_⟩
  · rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [hp a a le_rfl]
    · intro a b hab
      have hab' : a < b := hab
      simp [Matrix.diagonal_apply_ne _ hab'.ne, hp a b hab'.le]
  · convert hΛ a using 1
    simp [sub_smul, Finset.sum_sub_distrib, Matrix.diagonal_apply, ite_smul]

omit [NumberField K] in
theorem prod_smul_mem (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (aa : Fin r → Submodule (𝓞 K) K)
    (hF : IsFrame F Λ aa) (hF' : IsFrame F' Λ aa)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K))
    {j : ℕ} (hj : j ≤ r) (s t : Fin j → K) (hs : ∀ a, s a ∈ aa (Fin.castLE hj a))
    (ht : ∀ a, t a ∈ aa (Fin.castLE hj a)) {ξ : V} (hξ : ξ ∈ F.Xa j)
    (hp : ∀ y ∈ Λ, y ∈ F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    ((∏ a, s a) * Dl F F' j (hj.trans (Nat.le_succ r)) * star (∏ a, t a)) • ξ ∈ Λ := by
  obtain ⟨A, hA, hAΛ⟩ := exists_tri F Λ aa hF hj s hs
  obtain ⟨A', hA', hAΛ'⟩ := exists_tri F' Λ aa hF' hj t ht
  by_cases h0 : A.det = 0
  · rw [← hA, h0]; simp
  obtain ⟨q, -, rfl⟩ := Xa_coords F (hj.trans (Nat.le_succ r)) le_rfl hξ
  have hq : ∑ a, (Matrix.vecMul q A⁻¹) a • ∑ c, A a c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) =
      ∑ c, q c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) := by
    have : Matrix.vecMul (Matrix.vecMul q A⁻¹) A = q := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit h0), Matrix.vecMul_one]
    conv_rhs => rw [← this]
    generalize Matrix.vecMul q A⁻¹ = p
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have hX : ∀ b, ∑ c, A' b c • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) ∈ F'.X := fun b =>
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem_X F' (Fin.castLE hj c))
  have key := det_smul_mem H Λ _ _ hAΛ (fun a b => hint _ (hAΛ a) _ (hAΛ' b)) (Matrix.vecMul q A⁻¹)
    (fun b => by rw [hq]; exact hp _ (hAΛ' b) (hX b))
  rw [hq] at key
  convert key using 2
  rw [← hA, ← hA', ← Matrix.det_conjTranspose, Dl, ← Matrix.det_mul, ← Matrix.det_mul]
  congr 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, Matrix.submatrix_apply, Zhat, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, starRingEnd_apply]
  first
    | (refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Dl_ne (N : NF H r) : Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ≠ 0 := by
  have : (Zhat N.F N.F').submatrix (Fin.castLE (N.j_le.trans (Nat.le_succ r)))
      (Fin.castLE (N.j_le.trans (Nat.le_succ r))) = N.w.mat * Matrix.diagonal fun b => ((N.sgn b : ℤ) : K) := by
    ext a b
    simp [Zhat, N.pair, Matrix.mul_diagonal]
  rw [Dl, this, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (GlobalTheory.SgLoc.PtAlg.isUnit_det N.w).ne_zero (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
  exact_mod_cast (N.sgn b).ne_zero

theorem smul_mem_of_pairing (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      γ * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {ξ : V} (hξ : ξ ∈ N.F.Xa N.j) (hp : ∀ y ∈ Λ, y ∈ N.F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    γ • ξ ∈ Λ := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hΛ.1.2, mem_dual_iff] at hx
    exact hx.2
  have hD := Dl_ne N
  set D := Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) with hDdef
  set m : ℤ := 2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a) with hm
  let J : Submodule (𝓞 K) K := Λ.comap ((LinearMap.toSpanSingleton K V (D • ξ)).restrictScalars (𝓞 K))
  have h1 : ipow N.𝔡 (-m) ≤ J := by
    have e : -m = ∑ i : Fin N.j ⊕ Fin N.j,
        Sum.elim (fun a : Fin N.j => -((r : ℤ) - a.val)) (fun a : Fin N.j => -((r : ℤ) - a.val)) i := by
      rw [Fintype.sum_sum_type, hm, ← Fin.sum_univ_eq_sum_range (fun a : ℕ => (r : ℤ) - a)]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
      ring
    rw [e, ipow_sum _ N.𝔡_ne]
    refine prod_le_of_forall _ _ fun f hf => ?_
    have := prod_smul_mem N.F N.F' Λ N.aa hΛ.2.1 hΛ.2.2 hint N.j_le (fun a => f (Sum.inl a))
      (fun a => star (f (Sum.inr a))) (fun a => hf (Sum.inl a)) (fun a => ?_) hξ hp
    · show (∏ i, f i) • (D • ξ) ∈ Λ
      convert this using 1
      rw [smul_smul, Fintype.prod_sum_type, star_prod]
      simp only [star_star]
      congr 1; ring
    · have h2 := hf (Sum.inr a)
      have ha : a.val ≤ r := a.isLt.le.trans N.j_le
      have e2 : (r : ℤ) - a.val = ((r - a.val : ℕ) : ℤ) := by push_cast [ha]; ring
      show _ ∈ ipow N.𝔡 (-((r : ℤ) - a.val))
      simp only [Sum.elim_inr] at h2
      rw [e2] at h2 ⊢
      exact star_mem_ipow_neg _ N.𝔡_ne N.𝔡_star _ _ h2
  have h2 : ∀ w ∈ ipow N.𝔡 m * ipow N.𝔡 (-m), γ / D * w ∈ ipow N.𝔡 (-m) := by
    intro w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro y hy y' hy'
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hγ y hy)
      have : γ / D * (y * y') = o • y' := by rw [Algebra.smul_def, ho]; ring
      rw [this]; exact Submodule.smul_mem _ _ hy'
    · intro a b ha hb; rw [mul_add]; exact add_mem ha hb
  have h3 := h1 (h2 1 (by rw [← ipow_add _ N.𝔡_ne, add_neg_cancel, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩))
  have h4 : (γ / D * 1) • (D • ξ) ∈ Λ := h3
  rwa [smul_smul, mul_one, div_mul_cancel₀ _ hD] at h4

section Geometry
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def Ia (N : NF H r) (n : ℕ) : Submodule K V :=
  Submodule.span K ((fun b : Fin r => N.F.e b.castSucc) '' {b | N.j ≤ b.val ∧ b.val < n})

theorem e_mem_Ia (N : NF H r) (b : Fin r) {n : ℕ} (h : N.j ≤ b.val) (h' : b.val < n) :
    N.F.e b.castSucc ∈ Ia N n := Submodule.subset_span ⟨b, ⟨h, h'⟩, rfl⟩

theorem Ia_mono (N : NF H r) {m n : ℕ} (h : m ≤ n) : Ia N m ≤ Ia N n :=
  Submodule.span_mono (Set.image_mono fun _ hb => ⟨hb.1, lt_of_lt_of_le hb.2 h⟩)

theorem Ia_le (N : NF H r) (n : ℕ) : Ia N n ≤ N.F.Xa n :=
  Submodule.span_mono (Set.image_mono fun _ hb => hb.2)

theorem c_ne (N : NF H r) : N.c ≠ 0 := fun h => by simpa [h] using N.c_norm

theorem Ia_le' (N : NF H r) (n : ℕ) : Ia N n ≤ N.F'.Xa n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  have h := Submodule.smul_mem _ N.c⁻¹ (e_mem_Xa N.F' b hb.2)
  rw [N.same _ hb.1, smul_smul, inv_mul_cancel₀ (c_ne N), one_smul] at h
  exact h

theorem Ia_X (N : NF H r) {n : ℕ} {y : V} (h : y ∈ Ia N n) : y ∈ N.F.X := Xa_le_X _ _ (Ia_le N n h)
theorem Ia_X' (N : NF H r) {n : ℕ} {y : V} (h : y ∈ Ia N n) : y ∈ N.F'.X := Xa_le_X _ _ (Ia_le' N n h)

theorem Xa_le_sup (N : NF H r) (n : ℕ) : N.F.Xa n ≤ N.F.Xa N.j ⊔ Ia N n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  by_cases h : b.val < N.j
  · exact Submodule.mem_sup_left (e_mem_Xa N.F b h)
  · exact Submodule.mem_sup_right (e_mem_Ia N b (not_lt.1 h) hb)

theorem Xa_ist (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) : ∀ y ∈ N.F.Xa b.val, H.B y (N.ist b) = 0 :=
  perp_Xa N.F fun a ha => by rw [N.ist_e a b hb, if_neg (by rintro rfl; omega)]

theorem Ia_step (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {y : V} (hy : y ∈ Ia N (b.val + 1)) :
    y - H.B y (N.ist b) • N.F.e b.castSucc ∈ Ia N b.val := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    simp only [N.ist_e a b hb]
    split_ifs with h
    · subst h; simp
    · have : a.val ≠ b.val := fun h' => h (Fin.ext h')
      have h2 := ha.2
      simpa using e_mem_Ia N a ha.1 (show a.val < b.val by omega)
  | zero => simp
  | add y y' _ _ h h' =>
    convert add_mem h h' using 1
    simp only [map_add, LinearMap.add_apply]; module
  | smul a y _ h =>
    convert Submodule.smul_mem _ a h using 1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; module

theorem Ia_bot (N : NF H r) {n : ℕ} (h : n ≤ N.j) {y : V} (hy : y ∈ Ia N n) : y = 0 := by
  have : Ia N n ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have := hb.1; have := hb.2; omega
  exact this hy

theorem II_le (N : NF H r) : II N.F N.F' ≤ Ia N r := by
  intro x hx
  obtain ⟨ξ, hξ, i, hi, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N r hx.1)
  have hξ' : ξ ∈ N.F'.X := by simpa using sub_mem hx.2 (Ia_X' N hi)
  obtain ⟨p, -, rfl⟩ := Xa_coords N.F (N.j_le.trans (Nat.le_succ r)) le_rfl hξ
  have : p = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero (Dl_ne N) ?_
    funext b
    have := X_iso N.F' hξ' (e_mem_X N.F' (Fin.castLE N.j_le b))
    simpa [Matrix.vecMul, dotProduct, Zhat, map_sum] using this
  simpa [this] using hi

theorem hermForm_second_flag_X_z_eq_zero (N : NF H r) {y : V} (hy : y ∈ N.F'.X) : H.B y N.F.z = 0 := by
  have h := pairing_isotropicSpan_lastVector N.F' hy
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  rw [e, LinearMap.map_smulₛₗ, smul_eq_mul, mul_eq_zero] at h
  exact h.resolve_left (by simpa using c_ne N)

theorem eich_apply (x v : V) (c : K) (y : V) :
    eich H x v c y = y + H.B y v • x - H.B y x • v + (c * H.B y x) • x := by
  simp only [eich, xv, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, LinearMap.smul_apply]
  module

theorem eich_inN (F : FlagD H r) (x v : V) (c : K) (hx : x ∈ F.X) (hxv : H.B x v = 0)
    (hc : c + star c = -H.B v v) (hlev : ∀ a : Fin r, H.B (F.e a.castSucc) v • x ∈ F.Xa a.val) :
    F.InN (eich H x v c) := by
  obtain ⟨h1, h2, h3⟩ := eichlerMapIsometry K V H x v c (X_iso F hx hx) hxv hc
  refine ⟨h1, ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h3⟩, fun a => ?_, fun y hy => ?_⟩
  · simpa [eich_apply, e_X F _ hx] using hlev a
  · have : H.B y x = 0 := B_swap0 H (perp_X F hy x hx)
    simpa [eich_apply, this] using Submodule.smul_mem _ _ hx

def Gs (N : NF H r) : Subgroup (V ≃ₗ[K] V) := N.Rs ⊓ N.fixing (N.F.Xa N.j ⊔ N.F'.Xa N.j)

theorem exists_eich (N : NF H r) (x v : V) (c : K) (hx : x ∈ Ia N r) (hxv : H.B x v = 0)
    (hc : c + star c = -H.B v v)
    (hlev : ∀ a : Fin r, N.j ≤ a.val → H.B (N.F.e a.castSucc) v • x ∈ Ia N a.val)
    (h1 : ∀ a : Fin r, a.val < N.j → H.B (N.F.e a.castSucc) v = 0)
    (h2 : ∀ a : Fin r, a.val < N.j → H.B (N.F'.e a.castSucc) v = 0)
    (hW : v ∈ V0 N.F N.F' ⊔ N.Ist) :
    ∃ s ∈ Gs N, ∀ y, H.B y x = 0 → s y = y + H.B y v • x := by
  obtain ⟨-, e2, e3⟩ := eichlerMapIsometry K V H x v c (X_iso N.F (Ia_X N hx) (Ia_X N hx)) hxv hc
  let s : V ≃ₗ[K] V := LinearEquiv.ofLinear (eich H x v c) (eich H x (-v) (star c))
    (LinearMap.ext e3) (LinearMap.ext e2)
  have hs : ∀ y, H.B y x = 0 → s y = y + H.B y v • x := by
    intro y hy
    show eich H x v c y = _
    simp [eich_apply, hy]
  refine ⟨s, ⟨⟨Subgroup.subset_closure ⟨?_, ?_⟩, ?_⟩, ?_⟩, hs⟩
  · refine eich_inN N.F x v c (Ia_X N hx) hxv hc fun a => ?_
    by_cases h : a.val < N.j
    · simp [h1 a h]
    · exact Ia_le N _ (hlev a (not_lt.1 h))
  · refine eich_inN N.F' x v c (Ia_X' N hx) hxv hc fun a => ?_
    by_cases h : a.val < N.j
    · simp [h2 a h]
    · rw [N.same _ (not_lt.1 h), map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ _ (Ia_le' N _ (hlev a (not_lt.1 h)))
  · refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    have hy' := (mem_perp_iff H _ y).1 hy
    show s y = y
    rw [hs y (hy' x (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Ia_X N hx))))),
      hy' v hW]
    simp
  · refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    show s y = y
    rw [hs y (perp_sup H (fun u hu => X_iso N.F (Xa_le_X _ _ hu) (Ia_X N hx))
      (fun u hu => X_iso N.F' (Xa_le_X _ _ hu) (Ia_X' N hx)) y hy),
      perp_sup H (perp_Xa N.F h1) (perp_Xa N.F' h2) y hy]
    simp

theorem exists_shear (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {x : V} (hx : x ∈ Ia N b.val) :
    ∃ s ∈ Gs N, s N.F.z = N.F.z ∧ ∀ y ∈ N.F.X, s y = y + H.B y (N.ist b) • x := by
  obtain ⟨s, hs, h⟩ := exists_eich N x (N.ist b) 0 (Ia_mono N b.isLt.le hx) (Xa_ist N b hb x (Ia_le N _ hx))
    (by simp [N.ist_iso b b hb hb])
    (fun a _ => by
      rw [N.ist_e a b hb]
      split_ifs with h
      · subst h; simpa using hx
      · simp)
    (fun a ha => by rw [N.ist_e a b hb, if_neg (by rintro rfl; omega)])
    (fun a ha => N.ist_e' a b ha hb)
    (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
  refine ⟨s, hs, ?_, fun y hy => h y (X_iso N.F hy (Ia_X N hx))⟩
  rw [h _ (z_X N.F (Ia_X N hx)), N.normalForm_dual_orthogonal_last b hb]; simp

theorem exists_move_alt (N : NF H r) {x : V} (hx : x ∈ Ia N r) :
    ∃ s ∈ Gs N, s N.F.z = N.F.z - x ∧ ∀ y ∈ N.F.X, s y = y := by
  have hz : ∀ y, H.B y (star N.F.T⁻¹ • N.F.z) = N.F.T⁻¹ * H.B y N.F.z := by
    intro y; rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
  obtain ⟨s, hs, h⟩ := exists_eich N x (star N.F.T⁻¹ • N.F.z)
    (-H.B (star N.F.T⁻¹ • N.F.z) (star N.F.T⁻¹ • N.F.z) / 2) hx
    (by rw [hz, pairing_isotropicSpan_lastVector N.F (Ia_X N hx), mul_zero])
    (by rw [star_div₀, star_neg, H.herm, star_ofNat]; ring)
    (fun a _ => by rw [hz, pairing_isotropicSpan_lastVector N.F (e_mem_X _ _)]; simp)
    (fun a _ => by rw [hz, pairing_isotropicSpan_lastVector N.F (e_mem_X _ _)]; simp)
    (fun a _ => by rw [hz, hermForm_second_flag_X_z_eq_zero N (e_mem_X _ _)]; simp)
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert _ _)))))
  refine ⟨s, hs, ?_, fun y hy => ?_⟩
  · rw [h _ (z_X N.F (Ia_X N hx)), hz, pairing_lastVector_lastVector, mul_neg, inv_mul_cancel₀ N.F.hT]; module
  · rw [h _ (X_iso N.F hy (Ia_X N hx)), hz, pairing_isotropicSpan_lastVector N.F hy]; simp

theorem exists_unitri (N : NF H r) (v : Fin r → V)
    (hv : ∀ b : Fin r, N.j ≤ b.val → v b - N.F.e b.castSucc ∈ Ia N b.val) :
    ∃ u ∈ Gs N, u N.F.z = N.F.z ∧ ∀ b : Fin r, N.j ≤ b.val → u (v b) = N.F.e b.castSucc := by
  have key : ∀ m : ℕ, ∃ u ∈ Gs N, u N.F.z = N.F.z ∧ ∀ b : Fin r, N.j ≤ b.val →
      u (v b) = if r ≤ b.val + m then N.F.e b.castSucc else v b := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, rfl, fun b _ => by rw [if_neg (by have := b.isLt; omega)]; rfl⟩
    | succ m ih =>
      obtain ⟨u, hu, huz, h⟩ := ih
      by_cases hm : N.j + m + 1 ≤ r
      · let b0 : Fin r := ⟨r - m - 1, by omega⟩
        have hb0 : N.j ≤ b0.val := by show N.j ≤ r - m - 1; omega
        have hb1 : b0.val = r - m - 1 := rfl
        obtain ⟨s, hs, hsz, hs'⟩ := exists_shear N b0 hb0 (neg_mem (hv b0 hb0))
        refine ⟨s * u, mul_mem hs hu, by simp [huz, hsz], fun b hb => ?_⟩
        have hvX : v b ∈ N.F.Xa (b.val + 1) := by
          have := add_mem (Xa_mono N.F (Nat.le_succ _) (Ia_le N _ (hv b hb))) (e_mem_Xa N.F b (Nat.lt_succ_self _))
          simpa using this
        rw [LinearEquiv.mul_apply, h b hb]
        by_cases h1 : r ≤ b.val + m
        · rw [if_pos h1, if_pos (by omega), hs' _ (e_mem_X _ _), N.ist_e b b0 hb0,
            if_neg (by rintro rfl; omega)]
          simp
        · rw [if_neg h1, hs' _ (Xa_le_X _ _ hvX)]
          by_cases h2 : b = b0
          · subst h2
            have h3 := Xa_ist N b0 hb0 _ (Ia_le N _ (hv b0 hb0))
            rw [map_sub, LinearMap.sub_apply, N.ist_e b0 b0 hb0, if_pos rfl, sub_eq_zero] at h3
            rw [if_pos (by omega), h3]; simp
          · have h3 : b.val ≠ b0.val := fun h' => h2 (Fin.ext h')
            rw [if_neg (by omega), Xa_ist N b0 hb0 _ (Xa_mono N.F (by omega) hvX)]
            simp
      · refine ⟨u, hu, huz, fun b hb => ?_⟩
        rw [h b hb, if_pos (by omega), if_pos (by omega)]
  obtain ⟨u, hu, huz, h⟩ := key r
  exact ⟨u, hu, huz, fun b hb => by rw [h b hb, if_pos (by omega)]⟩

end Geometry

theorem level_ind (N : NF H r) (M Q : Submodule (𝓞 K) V) (w : Fin r → V)
    (hw : ∀ b : Fin r, N.j ≤ b.val → w b - N.F.e b.castSucc ∈ Ia N b.val)
    (h : ∀ b : Fin r, N.j ≤ b.val → ∀ y ∈ M, y ∈ Ia N (b.val + 1) →
      H.B y (N.ist b) • w b ∈ M ∧ H.B y (N.ist b) • w b ∈ Q) :
    ∀ n ≤ r, ∀ y ∈ M, y ∈ Ia N n → y ∈ Q := by
  intro n
  induction n with
  | zero => intro _ y _ hy; rw [Ia_bot N (Nat.zero_le _) hy]; exact zero_mem _
  | succ n ih =>
    intro hn y hyM hy
    by_cases hj : N.j ≤ n
    · let b : Fin r := ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := h b hj y hyM hy
      have h3 : y - H.B y (N.ist b) • w b ∈ Ia N n := by
        convert sub_mem (Ia_step N b hj hy) (Submodule.smul_mem _ (H.B y (N.ist b)) (hw b hj)) using 1
        module
      simpa using add_mem (ih (by omega) _ (sub_mem hyM h1) h3) h2
    · rw [Ia_bot N (by omega) hy]; exact zero_mem _

theorem smul_flag_vector_mem_reference_lattice (N : NF H r) (b : Fin r) {t : K} (ht : t ∈ N.aa b) : t • N.F.e b.castSucc ∈ N.P0 :=
  Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_iSup_of_mem b ⟨t, ht, rfl⟩)))

theorem hermForm_ist_mem_coeffIdeal_of_mem_reference (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {y : V} (hy : y ∈ N.P0) :
    H.B y (N.ist b) ∈ N.aa b := by
  have : N.P0 ≤ (N.aa b).comap ((H.B.flip (N.ist b)).restrictScalars (𝓞 K)) := by
    refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a ha => ?_)) ?_) (iSup₂_le fun a ha => ?_)
    all_goals
      rintro _ ⟨t, ht, rfl⟩
      show H.B (t • _) (N.ist b) ∈ N.aa b
      rw [map_smul, LinearMap.smul_apply]
    · rw [N.ist_e a b hb]
      split_ifs with h
      · subst h; simpa using ht
      · simp
    · simp [N.ist_e' a b ha hb]
    · simp [N.normalForm_dual_orthogonal_last b hb]
    · simp [N.ist_iso a b ha hb]
  exact this hy

theorem exists_adapted (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : Λ.FG) (b : Fin r) (hb : N.j ≤ b.val) :
    ∃ v, v - N.F.e b.castSucc ∈ Ia N b.val ∧
      ∀ y ∈ Λ, y ∈ Ia N (b.val + 1) → H.B y (N.ist b) • v ∈ Λ := by
  by_cases h0 : ∃ y ∈ Λ ⊓ rs (𝓞 K) (Ia N (b.val + 1)), H.B.flip (N.ist b) y ≠ 0
  · obtain ⟨v, hv, h1, h⟩ := exists_section _ (hΛ.of_le inf_le_left) _ h0
    have hv' : v ∈ Ia N (b.val + 1) := (Submodule.span_le.2 fun y hy => hy.2) hv
    refine ⟨v, ?_, fun y hy hy' => (h y ⟨hy, hy'⟩).1⟩
    have := Ia_step N b hb hv'
    rwa [show H.B v (N.ist b) = 1 from h1, one_smul] at this
  · push_neg at h0
    refine ⟨N.F.e b.castSucc, by simp, fun y hy hy' => ?_⟩
    rw [show H.B y (N.ist b) = 0 from h0 y ⟨hy, hy'⟩]; simp

theorem smul_add_mem (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : 𝓞 K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      (γ : K) * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {y ξ : V} (hy : ∀ u ∈ N.F'.X, H.B y u = 0) (hξ : ξ ∈ N.F.Xa N.j) (h : y - ξ ∈ Λ) : γ • y ∈ Λ := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hΛ.1.2, mem_dual_iff] at hx
    exact hx.2
  have h1 := smul_mem_of_pairing N Λ hΛ γ hγ hξ fun u hu hu' => by
    have := neg_mem (hint _ h u hu)
    simpa [hy u hu'] using this
  have h2 : γ • ξ ∈ Λ := by rw [← algebraMap_smul K γ ξ]; exact h1
  simpa [smul_sub] using add_mem (Λ.smul_mem γ h) h2

theorem normal_position : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ N.F.Xa N.j ⊔ N.F'.Xa N.j, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ 2 • (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ≤ Λ' ∧ Λ' ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 ∧ 𝔠 • line 1 N.F.z ≤ Λ' := by
  intro K V _ _ _ _ _ _ _ _ H _ r N g Λ _ hT 𝔠 _ _ _ h𝔠
  have hΛ := hT.1
  have hγ : ∀ γ ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      (γ : K) * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K) :=
    fun γ h y hy => (h𝔠 N.j _ le_rfl (Dl_ne N) γ h y hy).1
  have hfg : Λ.FG := ((isUnimod_iff H Λ).1 hΛ.1).1.fg
  choose! v hv hvΛ using exists_adapted N Λ hfg
  obtain ⟨u, hu, huz, huv⟩ := exists_unitri N v hv
  have hz : (1 : K) ∈ lead N.F Λ (Fin.last r) := by rw [hΛ.2.1.2]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 hz
  have he' : l + ξ = (1 : K) • N.F.z := he
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N r hξ)
  obtain ⟨E, hE, hEz, hEX⟩ := exists_move_alt N (neg_mem hξ₂)
  have hvX : ∀ b : Fin r, N.j ≤ b.val → v b ∈ Ia N r := fun b hb => by
    simpa using add_mem (Ia_mono N b.isLt.le (hv b hb)) (e_mem_Ia N b hb b.isLt)
  have hsv : ∀ b : Fin r, N.j ≤ b.val → ∀ t : K, (u * E) (t • v b) = t • N.F.e b.castSucc := fun b hb t => by
    rw [map_smul, LinearEquiv.mul_apply, hEX _ (Ia_X N (hvX b hb)), huv b hb]
  have hmem : ∀ y, y ∈ (u * E) • Λ ↔ ∃ x ∈ Λ, (u * E) x = y := fun y =>
    Submodule.mem_smul_pointwise_iff_exists _ _ _
  have hG := mul_mem hu hE
  refine ⟨u * E, hG.1, fun y hy => (mem_fixingSubgroup_iff _).1 hG.2 y hy, ?_⟩
  rintro _ rfl
  refine ⟨?_, ?_, ?_⟩
  · refine Submodule.smul_le.2 fun γ hγ2 y hy => ?_
    have hγ1 : γ ∈ 𝔠 := Ideal.pow_le_self two_ne_zero hγ2
    refine level_ind N N.P0 (((u * E) • Λ).comap (γ • LinearMap.id)) (fun b => N.F.e b.castSucc)
      (fun b _ => by simp) (fun b hb y hy _ => ?_) r le_rfl y hy.1 (II_le N hy.2)
    have ht := hermForm_ist_mem_coeffIdeal_of_mem_reference N b hb hy
    refine ⟨smul_flag_vector_mem_reference_lattice N b ht, ?_⟩
    generalize H.B y (N.ist b) = t at ht
    rw [← hΛ.2.1.1] at ht
    obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 ht
    have he' : l + ξ = t • N.F.e b.castSucc := he
    obtain ⟨η₁, hη₁, η₂, hη₂, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N b.val hξ)
    have hI : t • N.F.e b.castSucc - η₂ ∈ Ia N (b.val + 1) :=
      sub_mem (Submodule.smul_mem _ _ (e_mem_Ia N b hb (Nat.lt_succ_self _))) (Ia_mono N (Nat.le_succ _) hη₂)
    have h1 := smul_add_mem N Λ hΛ γ (hγ γ hγ1) (fun w hw => X_iso N.F' (Ia_X' N hI) hw) hη₁
      (by convert hl using 1; rw [← he']; abel)
    rw [← algebraMap_smul K γ] at h1
    have h2 := hvΛ b hb _ h1 (Submodule.smul_mem _ _ hI)
    show γ • (t • N.F.e b.castSucc) ∈ (u * E) • Λ
    refine (hmem _).2 ⟨_, h2, ?_⟩
    rw [hsv b hb, ← algebraMap_smul K γ (t • _), smul_smul, map_smul, map_sub, map_smul, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, N.ist_e b b hb, Xa_ist N b hb _ (Ia_le N _ hη₂), if_pos rfl,
      smul_eq_mul, smul_eq_mul, mul_one, sub_zero]
  · rintro y ⟨hy, hyI⟩
    obtain ⟨x, hx, rfl⟩ := (hmem y).1 hy
    have hxI : x ∈ Ia N r := by
      have : Ia N r ≤ (Ia N r).map ((u * E : V ≃ₗ[K] V) : V →ₗ[K] V) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨v b, hvX b hb.1, by simpa using hsv b hb.1 1⟩
      obtain ⟨x', hx', e⟩ := this (II_le N hyI)
      rwa [← (u * E).injective e]
    refine level_ind N Λ (N.P0.comap (((u * E : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K))) v hv
      (fun b hb y hy hy' => ⟨hvΛ b hb y hy hy', ?_⟩) r le_rfl x hx hxI
    show (u * E) (_ • v b) ∈ N.P0
    rw [hsv b hb]
    refine smul_flag_vector_mem_reference_lattice N b ?_
    rw [← hΛ.2.1.1]
    show H.B y (N.ist b) • N.F.e b.castSucc ∈ Λ ⊔ rs (𝓞 K) (N.F.Xa b.val)
    have := sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right (S := Λ)
      (show _ ∈ rs (𝓞 K) (N.F.Xa b.val) from Ia_le N _ (Ia_step N b hb hy')))
    simpa using this
  · refine Submodule.smul_le.2 ?_
    rintro γ hγ1 _ ⟨t, ht, rfl⟩
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 ht
    have h1 := smul_add_mem N Λ hΛ γ (hγ γ hγ1) (y := N.F.z - ξ₂)
      (fun w hw => by
        rw [map_sub, LinearMap.sub_apply, B_swap0 H (hermForm_second_flag_X_z_eq_zero N hw), X_iso N.F' (Ia_X' N hξ₂) hw, sub_zero]) hξ₁
      (by convert hl using 1; rw [one_smul] at he'; rw [← he']; abel)
    show γ • (algebraMap (𝓞 K) K o • N.F.z) ∈ (u * E) • Λ
    rw [algebraMap_smul, smul_comm]
    refine Submodule.smul_mem _ _ ((hmem _).2 ⟨_, h1, ?_⟩)
    rw [← algebraMap_smul K γ, ← algebraMap_smul K γ N.F.z, map_smul, LinearEquiv.mul_apply, map_sub, hEz,
      hEX _ (Ia_X N hξ₂)]
    simp [huz]

end GlobalTheory.DegCnt.PosIso
end
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_form_ideal_divisibility : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ N.F.Xa N.j ⊔ N.F'.Xa N.j, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ 2 • (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ≤ Λ' ∧ Λ' ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 ∧ 𝔠 • line 1 N.F.z ≤ Λ' := by
  atlas_forward_decl GlobalTheory.DegCnt.PosIso.normal_position
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.DegCnt.DualPos

section Generic
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

def Bd {E : Type} [AddCommGroup E] [Module R E] (I : Ideal R) (M : Submodule R E) : Submodule R E where
  carrier := {v | ∀ a ∈ I, a • v ∈ M}
  add_mem' := fun {x y} hx hy a ha => by rw [smul_add]; exact M.add_mem (hx a ha) (hy a ha)
  zero_mem' := fun a _ => by simp
  smul_mem' := fun b x hx a ha => by rw [smul_comm]; exact M.smul_mem b (hx a ha)

theorem bd_add {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M : Submodule R E} {v : E} {n m : ℕ}
    (h : v ∈ Bd (c ^ n) (Bd (c ^ m) M)) : v ∈ Bd (c ^ (n + m)) M := by
  intro a ha
  rw [pow_add] at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro x hx y hy
    rw [mul_comm, mul_smul]
    exact h x hx y hy
  · intro x y hx hy
    rw [add_smul]; exact M.add_mem hx hy

theorem bd_mono {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M : Submodule R E} {v : E} {n m : ℕ}
    (h : v ∈ Bd (c ^ n) M) (hnm : n ≤ m) : v ∈ Bd (c ^ m) M :=
  fun a ha => h a (Ideal.pow_le_pow_right hnm ha)

theorem bd_self {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M : Submodule R E} {v : E}
    (h : v ∈ M) : v ∈ Bd c M := fun a _ => M.smul_mem a h

theorem smul_le_iff {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M M' : Submodule R E} :
    c • M ≤ M' ↔ ∀ v ∈ M, v ∈ Bd c M' := by
  rw [Submodule.smul_le]
  exact ⟨fun h v hv a ha => h a ha v hv, fun h a ha v hv => h v hv a ha⟩

def StarSt (K : Type) [Field K] [StarRing K] [Algebra R K] (I : Ideal R) : Prop :=
  ∀ x ∈ I, ∃ y ∈ I, algebraMap R K y = star (algebraMap R K x)

theorem starSt_pow {c : Ideal R} (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c) (n : ℕ) : StarSt K (c ^ n) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    intro a ha
    rw [pow_succ] at ha ⊢
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      obtain ⟨x', hx', ex⟩ := ih x hx
      obtain ⟨y', hy', ey⟩ := hc y hy
      exact ⟨x' * y', Ideal.mul_mem_mul hx' hy', by simp [ex, ey]⟩
    · rintro x y ⟨x', hx', ex⟩ ⟨y', hy', ey⟩
      exact ⟨x' + y', Ideal.add_mem _ hx' hy', by simp [ex, ey]⟩

theorem star_one_mem (h1 : StarSt K (⊤ : Ideal R)) {x : K} (hx : x ∈ (1 : Submodule R K)) :
    star x ∈ (1 : Submodule R K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hx
  obtain ⟨b, -, hb⟩ := h1 a trivial
  exact Submodule.mem_one.2 ⟨b, hb⟩

theorem star_bd {c : Ideal R} (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c) {n : ℕ} {x : K}
    (hx : x ∈ Bd (c ^ n) (1 : Submodule R K)) : star x ∈ Bd (c ^ n) (1 : Submodule R K) := by
  intro a ha
  obtain ⟨b, hb, e⟩ := starSt_pow h1 hc n a ha
  have := star_one_mem h1 (hx b hb)
  rw [Algebra.smul_def, e, star_mul', star_star] at this
  rwa [Algebra.smul_def]

theorem B_smul (H : HermSpace K V) (a : R) (v w : V) : H.B (a • v) w = a • H.B v w := by
  rw [← algebraMap_smul K a v, map_smul, LinearMap.smul_apply, algebraMap_smul]

theorem pair_left (H : HermSpace K V) {c : Ideal R} {M : Submodule R V} {n k : ℕ} {v w : V}
    (hv : v ∈ Bd (c ^ n) M) (h : ∀ x ∈ M, H.B x w ∈ Bd (c ^ k) (1 : Submodule R K)) :
    H.B v w ∈ Bd (c ^ (n + k)) (1 : Submodule R K) := by
  refine bd_add fun a ha => ?_
  rw [← B_smul]
  exact h _ (hv a ha)

theorem pair_both (H : HermSpace K V) {c : Ideal R} (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c)
    {M : Submodule R V} {n m k : ℕ} {v w : V}
    (hv : v ∈ Bd (c ^ n) M) (hw : w ∈ Bd (c ^ m) M)
    (h : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ Bd (c ^ k) (1 : Submodule R K)) :
    H.B v w ∈ Bd (c ^ (n + (m + k))) (1 : Submodule R K) := by
  refine pair_left H hv fun x hx => ?_
  rw [← H.herm]
  exact star_bd h1 hc (pair_left H hw fun y hy => h y hy x hx)

theorem of_dual (H : HermSpace K V) {c : Ideal R} {M : Submodule R V} (hk : c • dual H M ≤ M) {n : ℕ} {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) (h : ∀ x ∈ M, H.B v x ∈ Bd (c ^ n) (1 : Submodule R K)) :
    v ∈ Bd (c ^ (n + 1)) M := by
  refine bd_add fun a ha => ?_
  rw [pow_one]
  refine smul_le_iff.1 hk _ ((mem_dual_iff H M _).2 ⟨?_, fun x hx => ?_⟩)
  · rw [← algebraMap_smul K a v]; exact Submodule.smul_mem _ _ hv
  · rw [B_smul]; exact h x hx a ha

def pr (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) : V →ₗ[K] V :=
  ∑ b, (H.B.flip (e b)).smulRight (f b)

omit [Module R V] [IsScalarTower R K V] in
theorem pr_apply (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (v : V) :
    pr H e f v = ∑ b, H.B v (e b) • f b := by
  simp [pr, LinearMap.sum_apply]

theorem pr_adj (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (x v : V) :
    H.B (pr H f e x) v = H.B x (pr H e f v) := by
  simp only [pr_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← H.herm v (e b), mul_comm]; rfl

theorem pr_comp (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (Φ : V →ₗ[K] V) (v : V) :
    pr H e (Φ ∘ f) v = Φ (pr H e f v) := by
  simp [pr_apply]

theorem pr_mem (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (v : V) :
    pr H e f v ∈ Submodule.span K (Set.range f) := by
  rw [pr_apply]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem pr_zero (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) {v : V} (hv : ∀ b, H.B v (e b) = 0) :
    pr H e f v = 0 := by
  simp [pr_apply, hv]

theorem span_perp (H : HermSpace K V) {J : Type} {e : J → V} {w : V} (hw : ∀ b, H.B (e b) w = 0) {v : V}
    (hv : v ∈ Submodule.span K (Set.range e)) : H.B v w = 0 := by
  have : Submodule.span K (Set.range e) ≤ LinearMap.ker (H.B.flip w) := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact hw b
  exact this hv

theorem pr_fix (H : HermSpace K V) {J : Type} [Fintype J] [DecidableEq J] {e f : J → V}
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) {v : V}
    (hv : v ∈ Submodule.span K (Set.range f)) : pr H e f v = v := by
  have : Submodule.span K (Set.range f) ≤ LinearMap.eqLocus (pr H e f) LinearMap.id := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩
    show pr H e f (f b) = f b
    rw [pr_apply, Finset.sum_eq_single b]
    · rw [← H.herm, hef]; simp
    · intro a _ hab; rw [← H.herm, hef]; simp [hab]
    · simp
  exact this hv

theorem exists_skew (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V)
    (hee : ∀ a b, H.B (e a) (e b) = 0) (Φ : V →ₗ[K] V) (t : K) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ (∀ v, v - s v ∈ Submodule.span K (Set.range e)) ∧
      (∀ v, pr H e f v = 0 → s v = v) ∧
      ∀ v w, H.B (v - s v) w =
        star t * H.B (Φ (pr H e f v)) (pr H e f w) - t * H.B (pr H e f v) (Φ (pr H e f w)) := by
  set p := pr H e f with hp
  let N : V →ₗ[K] V := (star t • (pr H f e ∘ₗ Φ) - t • pr H (Φ ∘ f) e) ∘ₗ p
  have hN : ∀ v, N v = star t • pr H f e (Φ (p v)) - t • pr H (Φ ∘ f) e (p v) := fun v => rfl
  have hmem : ∀ v, N v ∈ Submodule.span K (Set.range e) := fun v => by
    rw [hN]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (pr_mem H _ _ _)) (Submodule.smul_mem _ _ (pr_mem H _ _ _))
  have h0 : ∀ v, p v = 0 → N v = 0 := fun v hv => by rw [hN, hv]; simp
  have hpN : ∀ v, p (N v) = 0 := fun v => pr_zero H e f fun b => span_perp H (fun a => hee a b) (hmem v)
  have hB : ∀ v w, H.B (N v) w = star t * H.B (Φ (p v)) (p w) - t * H.B (p v) (Φ (p w)) := fun v w => by
    rw [hN, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      pr_adj, pr_adj, pr_comp]
    rfl
  refine ⟨LinearEquiv.ofLinear (LinearMap.id - N) (LinearMap.id + N) ?_ ?_, ?_, ?_, ?_, ?_⟩
  · ext v; simp [h0 _ (hpN v)]
  · ext v; simp [h0 _ (hpN v)]
  · intro x y
    have e1 : H.B (N x) (N y) = 0 := by rw [hB, hpN]; simp
    have e2 : H.B x (N y) = - H.B (N x) y := by
      rw [← H.herm, hB, hB]; simp [H.herm]
    simp [e1, e2]
  · intro v; simpa using hmem v
  · intro v hv; simp [h0 v hv]
  · intro v w; simpa using hB v w

theorem core (H : HermSpace K V) {J : Type} [Fintype J] [DecidableEq J] (e f : J → V)
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) (hee : ∀ a b, H.B (e a) (e b) = 0)
    (hff : ∀ a b, H.B (f a) (f b) = 0) (P A M Λ : Submodule R V) (Pi : Submodule K V)
    (hPi : Submodule.span K (P : Set V) = Pi) (c : Ideal R) (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c)
    (n : ℕ) (t : R) (ht : algebraMap R K t + star (algebraMap R K t) = 1)
    (hA : A ≤ P) (hM : M ≤ P) (hdec : ∀ x ∈ P, ∃ a ∈ A, ∃ m ∈ M, x = a + m)
    (hAe : ∀ x ∈ A, ∀ b, H.B x (e b) = 0) (hMf : ∀ y ∈ M, y ∈ Submodule.span K (Set.range f))
    (heP : ∀ b, e b ∈ Pi) (hAΛ : ∀ x ∈ A, x ∈ Bd (c ^ n) Λ)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule R K))
    (hk1 : c • dual H P ≤ P) (hk2 : c • P ≤ dual H P) (Φ : V →ₗ[K] V)
    (hΦ1 : ∀ y ∈ M, Φ y ∈ Pi) (hΦ2 : ∀ y ∈ M, ∀ b, H.B (Φ y - y) (e b) = 0)
    (hΦ3 : ∀ y ∈ M, Φ y ∈ Bd (c ^ 4) Λ) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ (∀ v, v - s v ∈ Submodule.span K (Set.range e)) ∧
      (∀ v, (∀ b, H.B v (e b) = 0) → s v = v) ∧
      (∀ x ∈ P, x ∈ Bd (c ^ (3 * n + 12)) (s • Λ)) ∧
      ∀ x ∈ s • Λ, x ∈ Pi → x ∈ Bd (c ^ (3 * n + 13)) P := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_skew H e f hee Φ (algebraMap R K t)
  set p := pr H e f with hp
  set q := pr H f e with hq
  have hsI : ∀ v, (∀ b, H.B v (e b) = 0) → s v = v := fun v hv => hs3 v (pr_zero H e f hv)
  have hPP : ∀ x ∈ P, ∀ y ∈ P, H.B x y ∈ Bd (c ^ 1) (1 : Submodule R K) := by
    intro x hx y hy a ha
    rw [pow_one] at ha
    rw [← B_smul]
    exact ((mem_dual_iff H P _).1 (smul_le_iff.1 hk2 x hx a ha)).2 y hy
  have hLL : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ Bd (c ^ 0) (1 : Submodule R K) := fun x hx y hy =>
    bd_self (hint x hx y hy)
  have hPPi : ∀ x ∈ P, x ∈ Pi := fun x hx => hPi ▸ Submodule.subset_span hx
  have hePi : Submodule.span K (Set.range e) ≤ Pi := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact heP b
  have hpM : ∀ y ∈ M, p y = y := fun y hy => pr_fix H hef (hMf y hy)
  have hpA : ∀ x ∈ A, p x = 0 := fun x hx => pr_zero H e f (hAe x hx)
  have hpw : ∀ y ∈ M, p (Φ y - y) = 0 := fun y hy => pr_zero H e f (hΦ2 y hy)
  have hpe : ∀ v ∈ Submodule.span K (Set.range e), p v = 0 := fun v hv =>
    pr_zero H e f fun b => span_perp H (fun a => hee a b) hv
  have hqB : ∀ v w, H.B (q v) w = H.B v (p w) := pr_adj H e f
  have hMM : ∀ y ∈ M, ∀ x ∈ M, H.B y x = 0 := fun y hy x hx =>
    span_perp H (fun b => by rw [← H.herm, span_perp H (fun a => hff a b) (hMf x hx), star_zero]) (hMf y hy)
  have hwA : ∀ y ∈ M, ∀ x ∈ A, H.B (Φ y - y) x ∈ Bd (c ^ (n + 4)) (1 : Submodule R K) := by
    intro y hy x hx
    rw [map_sub, LinearMap.sub_apply]
    exact Submodule.sub_mem _ (bd_mono (pair_both H h1 hc (hΦ3 y hy) (hAΛ x hx) hLL) (by omega))
      (bd_mono (hPP y (hM hy) x (hA hx)) (by omega))
  have hwPi : ∀ y ∈ M, Φ y - y ∈ Pi := fun y hy => Pi.sub_mem (hΦ1 y hy) (hPPi y (hM hy))
  have hu : ∀ y ∈ M, (Φ y - y) - q (Φ y - y) ∈ Bd (c ^ (n + 4 + 1)) P := by
    intro y hy
    refine of_dual H hk1 (hPi ▸ Pi.sub_mem (hwPi y hy) (hePi (pr_mem H _ _ _))) fun x hx => ?_
    obtain ⟨a, ha, m, hm, rfl⟩ := hdec x hx
    rw [map_sub, LinearMap.sub_apply, hqB, map_add p, hpA a ha, hpM m hm, zero_add, map_add, add_sub_cancel_right]
    exact hwA y hy a ha
  have hww : ∀ y ∈ M, ∀ x ∈ M, H.B (Φ y - y) (Φ x - x) ∈ Bd (c ^ (2 * n + 11)) (1 : Submodule R K) := by
    intro y hy x hx
    have h := pair_both H h1 hc (hu y hy) (hu x hx) hPP
    have e1 : H.B (q (Φ y - y)) (Φ x - x - q (Φ x - x)) = 0 := by
      rw [hqB, map_sub p, hpw x hx, hpe _ (pr_mem H _ _ _)]; simp
    have e2 : H.B (Φ y - y) (q (Φ x - x)) = 0 := by
      rw [← H.herm, hqB, hpw y hy]; simp
    rw [map_sub H.B, LinearMap.sub_apply, e1, sub_zero, map_sub (H.B _), e2, sub_zero] at h
    exact bd_mono h (by omega)
  have hz : ∀ y ∈ M, s (Φ y) - y ∈ Bd (c ^ (2 * n + 11 + 1)) P := by
    intro y hy
    have hpy : p (Φ y) = y := by
      have := hpw y hy
      rwa [map_sub, hpM y hy, sub_eq_zero] at this
    have hz0 : s (Φ y) - y = (Φ y - y) - (Φ y - s (Φ y)) := by abel
    rw [hz0]
    refine of_dual H hk1 (hPi ▸ Pi.sub_mem (hwPi y hy) (hePi (hs2 _))) fun x hx => ?_
    obtain ⟨a, ha, m, hm, rfl⟩ := hdec x hx
    rw [map_sub, LinearMap.sub_apply, hs4, map_add p, hpA a ha, hpM m hm, zero_add, map_add, hpy]
    have e1 : H.B (Φ y - y) a + H.B (Φ y - y) m -
        (star (algebraMap R K t) * H.B (Φ y) m - algebraMap R K t * H.B y (Φ m)) =
        H.B (Φ y - y) a + t • (H.B (Φ y) (Φ m) - H.B (Φ y - y) (Φ m - m)) := by
      have : star (algebraMap R K t) = 1 - algebraMap R K t := by rw [← ht]; ring
      rw [this, Algebra.smul_def]
      simp only [map_sub, LinearMap.sub_apply, hMM y hy m hm]
      ring
    rw [e1]
    exact Submodule.add_mem _ (bd_mono (hwA y hy a ha) (by omega)) (Submodule.smul_mem _ _
      (Submodule.sub_mem _ (bd_mono (pair_both H h1 hc (hΦ3 y hy) (hΦ3 m hm) hLL) (by omega)) (hww y hy m hm)))
  have hmem : ∀ x, x ∈ s • Λ ↔ ∃ l ∈ Λ, s l = x := fun x => Submodule.mem_smul_pointwise_iff_exists _ _ _
  have hsR : ∀ (a : R) v, s (a • v) = a • s v := fun a v => by
    rw [← algebraMap_smul K a v, map_smul, algebraMap_smul]
  have hAs : ∀ x ∈ A, x ∈ Bd (c ^ n) (s • Λ) := by
    intro x hx a ha
    exact (hmem _).2 ⟨_, hAΛ x hx a ha, hs3 _ (hpA _ (A.smul_mem a hx))⟩
  have hMs : ∀ y ∈ M, y ∈ Bd (c ^ (3 * n + 12)) (s • Λ) := by
    intro y hy
    have e1 : y = s (Φ y) - (s (Φ y) - y) := by abel
    rw [e1]
    refine Submodule.sub_mem _ (bd_mono (n := 4) ?_ (by omega)) (bd_mono (n := 2 * n + 11 + 1 + n) ?_ (by omega))
    · intro a ha
      exact (hmem _).2 ⟨_, hΦ3 y hy a ha, hsR _ _⟩
    · refine bd_add fun a ha => hAs _ ?_
      obtain ⟨x, hx, m, hm, h⟩ := hdec _ (hz y hy a ha)
      have hz0 : s (Φ y) - y = (Φ y - y) - (Φ y - s (Φ y)) := by abel
      have h2 : p (x + m) = 0 := by
        rw [← h, ← algebraMap_smul K a, map_smul, hz0, map_sub p, hpw y hy, hpe _ (hs2 _)]; simp
      rw [map_add, hpA x hx, hpM m hm, zero_add] at h2
      rw [h, h2, add_zero]; exact hx
  have hP : ∀ x ∈ P, x ∈ Bd (c ^ (3 * n + 12)) (s • Λ) := by
    intro x hx
    obtain ⟨a, ha, m, hm, rfl⟩ := hdec x hx
    exact Submodule.add_mem _ (bd_mono (hAs a ha) (by omega)) (hMs m hm)
  refine ⟨s, hs1, hs2, hsI, hP, fun x hx hxP => ?_⟩
  refine of_dual H hk1 (n := 3 * n + 12) (hPi ▸ hxP) fun y hy => ?_
  refine bd_mono (pair_both H h1 hc (n := 0) (k := 0) (bd_self hx) (hP y hy) ?_) (by omega)
  intro u hu v hv
  obtain ⟨u', hu', rfl⟩ := (hmem u).1 hu
  obtain ⟨v', hv', rfl⟩ := (hmem v).1 hv
  rw [hs1]
  exact hLL _ hu' _ hv'

end Generic

section Integers
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

theorem exists_ext (L : Submodule (𝓞 K) V) (σ : L →ₗ[𝓞 K] V) : ∃ Ψ : V →ₗ[K] V, ∀ y : L, Ψ y = σ y := by
  have hB : Module.Baer (𝓞 K) V := by
    intro I g
    by_cases hI : I = ⊥
    · refine ⟨0, fun x hx => ?_⟩
      have : (⟨x, hx⟩ : I) = 0 := Subtype.ext (by simpa [hI] using hx)
      rw [this]; simp
    · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      have ha1 : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha0
      refine ⟨LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • g ⟨a, ha⟩), fun x hx => ?_⟩
      have h : x • g ⟨a, ha⟩ = a • g ⟨x, hx⟩ := by
        rw [← map_smul, ← map_smul]; congr 1; ext; simp [mul_comm]
      rw [LinearMap.toSpanSingleton_apply, smul_comm, h, ← algebraMap_smul K a, inv_smul_smul₀ ha1]
  obtain ⟨h, hh⟩ := hB.extension_property L.subtype L.injective_subtype σ
  exact ⟨LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K h, fun y => LinearMap.congr_fun hh y⟩

theorem exists_lift [FiniteDimensional K V] (H : HermSpace K V) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    {J : Type} [Fintype J] [DecidableEq J] {e f : J → V}
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hLf : ∀ y ∈ L, y ∈ Submodule.span K (Set.range f))
    (hint : ∀ y ∈ L, ∀ x ∈ Λ ⊓ rs (𝓞 K) (Submodule.span K (Set.range e)), H.B x y ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ Ψ : V →ₗ[K] V, ∀ y ∈ L, Ψ y ∈ Λ ∧ ∀ b, H.B (Ψ y - y) (e b) = 0 := by
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  let p : V →ₗ[𝓞 K] V := (pr H e f).restrictScalars (𝓞 K)
  let N : Submodule (𝓞 K) V := Λ ⊓ L.comap p
  let ρ : N →ₗ[𝓞 K] L := p.restrict fun x hx => hx.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    have hx : ∀ x : ↥(Λ ⊓ rs (𝓞 K) (Submodule.span K (Set.range e))), IsIntegral ℤ (H.B x y) := fun x =>
      (GlobalTheory.UnimodQuot.mem_one_iff _).1 (hint y hy x x.2)
    let φ : ↥(Λ ⊓ rs (𝓞 K) (Submodule.span K (Set.range e))) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x y, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) y = H.B a y + H.B b y
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) y = algebraMap (𝓞 K) K a * H.B b y
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨l, hl, h'⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU _ φ
    have hb : ∀ b, H.B (l - y) (e b) = 0 := by
      intro b
      obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hΛ (e b)
      have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have hs' : algebraMap (𝓞 K) K s • e b ∈ Λ := by rw [algebraMap_smul]; exact hs
      have h1 : H.B (algebraMap (𝓞 K) K s • e b) l = H.B (algebraMap (𝓞 K) K s • e b) y :=
        h' ⟨_, hs', (Submodule.span K (Set.range e)).smul_mem _ (Submodule.subset_span (Set.mem_range_self b))⟩
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [← H.herm, map_sub, smul_right_injective K hs0 h1, sub_self, star_zero]
    have hpl : pr H e f l = y := by
      have := pr_zero H e f hb
      rwa [map_sub, pr_fix H hef (hLf y hy), sub_eq_zero] at this
    exact ⟨⟨l, hl, show pr H e f l ∈ L from hpl ▸ hy⟩, Subtype.ext hpl⟩
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property ρ LinearMap.id hρ
  obtain ⟨Ψ, hΨ⟩ := exists_ext L (N.subtype ∘ₗ σ)
  refine ⟨Ψ, fun y hy => ?_⟩
  have h1 : Ψ y = σ ⟨y, hy⟩ := hΨ ⟨y, hy⟩
  have h2 : pr H e f (σ ⟨y, hy⟩) = y := congrArg Subtype.val (LinearMap.congr_fun hσ ⟨y, hy⟩)
  refine ⟨h1 ▸ (σ ⟨y, hy⟩).2.1, fun b => ?_⟩
  have h3 : pr H e f (Ψ y - y) = 0 := by rw [map_sub, h1, h2, pr_fix H hef (hLf y hy), sub_self]
  have h4 := pr_adj H e f (e b) (Ψ y - y)
  have h5 := pr_adj H f e (Ψ y - y) (e b)
  rw [h3, pr_fix H (e := f) (f := e) ?_ (Submodule.subset_span ⟨b, rfl⟩)] at h5
  · simpa using h5.symm
  · intro a a'
    rw [← H.herm, hef]
    by_cases h : a = a' <;> simp [h, eq_comm]

theorem mem_line {A : Submodule (𝓞 K) K} {v x : V} : x ∈ line A v ↔ ∃ a ∈ A, a • v = x := by
  simp [line]

theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (hv : v ∈ S) : line A v ≤ rs (𝓞 K) S := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := mem_line.1 hx
  exact S.smul_mem a hv

theorem mem_span_of_line {A : Submodule (𝓞 K) K} (hA : A ≠ ⊥) {v : V} {P : Submodule (𝓞 K) V}
    (h : line A v ≤ P) : v ∈ Submodule.span K (P : Set V) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  rw [← Submodule.smul_mem_iff _ ha0]
  exact Submodule.subset_span (h (mem_line.2 ⟨a, ha, rfl⟩))

theorem ipow_ne_bot {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) : ipow 𝔡 n ≠ ⊥ := by
  unfold ipow
  rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  exact zpow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.2 h)

theorem ipow_fg (𝔡 : Ideal (𝓞 K)) (n : ℤ) : (ipow 𝔡 n).FG := by
  unfold ipow
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _

theorem lift_bd {H : HermSpace K V} {r : ℕ} (N : NF H r) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    (hL : IsLift N.F N.F' N.Wt) (hsp : N.Split Λ) {c : Ideal (𝓞 K)}
    (hk : c • dual H (latTh N.F N.F' Λ) ≤ latTh N.F N.F' Λ) {l v : V} (hl : l ∈ Λ) (hv : v ∈ N.Pi)
    (hw : l - v ∈ N.Wt) : v ∈ Bd c Λ := by
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  have hII : II N.F N.F' ≤ V0 N.F N.F' := inf_le_left.trans (le_sup_left.trans le_sup_left)
  unfold NF.Split at hsp
  rw [hsp] at hk
  have hd : l - v ∈ dual H ((Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F')) := by
    rw [mem_dual_iff]
    constructor
    · obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hΛ (l - v)
      have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have hs' : algebraMap (𝓞 K) K s • (l - v) ∈ Λ := by rw [algebraMap_smul]; exact hs
      rw [← Submodule.smul_mem_iff _ hs0]
      exact Submodule.subset_span (Submodule.mem_sup_left ⟨hs', N.Wt.smul_mem _ hw⟩)
    · intro x hx
      obtain ⟨a, ⟨ha, haW⟩, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
      have e1 : H.B (l - v) i = 0 := by rw [← H.herm, hL.1 _ hw i (hII hi), star_zero]
      have e2 : H.B v a = 0 := (mem_perp_iff H _ v).1 hv a haW
      rw [map_add, e1, add_zero, map_sub, LinearMap.sub_apply, e2, sub_zero]
      rw [← hU.2] at hl
      exact ((mem_dual_iff H Λ l).1 hl).2 a ha
  intro a ha
  obtain ⟨x, ⟨hx, hxW⟩, i, hi, h⟩ := Submodule.mem_sup.1 (smul_le_iff.1 hk _ hd a ha)
  have hiW : i ∈ N.Wt ⊓ II N.F N.F' := by
    refine ⟨?_, hi⟩
    rw [eq_sub_of_add_eq' h]
    exact (rs (𝓞 K) N.Wt).sub_mem ((rs (𝓞 K) N.Wt).smul_mem a hw) hxW
  rw [hL.2.1, Submodule.mem_bot] at hiW
  rw [hiW, add_zero, smul_sub] at h
  have : a • v = a • l - x := by rw [h]; abel
  rw [this]
  exact Λ.sub_mem (Λ.smul_mem a hl) hx

theorem e_mem_X {H : HermSpace K V} {r : ℕ} (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

theorem c_ne {H : HermSpace K V} {r : ℕ} (N : NF H r) : N.c ≠ 0 := by
  intro h
  have := N.c_norm
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem e_mem_II {H : HermSpace K V} {r : ℕ} (N : NF H r) (a : Fin r) (ha : N.j ≤ a.val) :
    N.F.e a.castSucc ∈ II N.F N.F' := by
  refine ⟨e_mem_X _ a, ?_⟩
  have := e_mem_X N.F' a
  rw [N.same _ (by simpa using ha)] at this
  exact (Submodule.smul_mem_iff _ (c_ne N)).1 this

def dualPart {H : HermSpace K V} {r : ℕ} (N : NF H r) : Submodule (𝓞 K) V :=
  ⨆ a : Fin r, ⨆ _ : N.j ≤ a.val, line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)

theorem dualPart_fg {H : HermSpace K V} {r : ℕ} (N : NF H r) : (dualPart N).FG :=
  Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _

theorem hermFramePair_lattice_decomposes_dualSpanPart {H : HermSpace K V} {r : ℕ} (N : NF H r) :
    ∀ x ∈ N.P0, ∃ a ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), ∃ m ∈ dualPart N, x = a + m := by
  intro x hx
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨a, ⟨Submodule.mem_sup_left ha, ?_⟩, m, hm, rfl⟩
  refine (show _ ≤ rs (𝓞 K) (V0 N.F N.F') from sup_le (sup_le (iSup_le fun a => line_le ?_)
    (iSup_le fun a => iSup_le fun _ => line_le ?_)) (line_le ?_)) ha
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a))
  · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem dualPart_le {H : HermSpace K V} {r : ℕ} (N : NF H r) : dualPart N ≤ rs (𝓞 K) N.Ist :=
  iSup_le fun a => iSup_le fun ha => line_le (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem span_hermFramePair_lattice_eq_sup {H : HermSpace K V} {r : ℕ} (N : NF H r) :
    Submodule.span K (N.P0 : Set V) = V0 N.F N.F' ⊔ N.Ist := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, m, hm, rfl⟩ := hermFramePair_lattice_decomposes_dualSpanPart N x hx
    exact Submodule.add_mem_sup ha.2 (dualPart_le N hm)
  have he : ∀ a : Fin r, N.F.e a.castSucc ∈ Submodule.span K (N.P0 : Set V) := fun a =>
    mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a))))
  have hz : N.F.z ∈ Submodule.span K (N.P0 : Set V) :=
    mem_span_of_line (A := 1) (fun h => one_ne_zero ((Submodule.mem_bot (𝓞 K)).1
      (h ▸ Submodule.mem_one.2 ⟨1, map_one _⟩ : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K)))) (le_sup_of_le_left le_sup_right)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, -, rfl⟩
    exact he a
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, -, rfl⟩
    by_cases ha : a.val < N.j
    · exact mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
        (le_iSup₂_of_le (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha le_rfl))))
    · show N.F'.e a.castSucc ∈ _
      rw [N.same _ (by simpa using ha)]
      exact Submodule.smul_mem _ _ (he a)
  · refine Submodule.span_le.2 ?_
    rintro _ (rfl | rfl)
    · exact hz
    · show N.F'.e (Fin.last r) ∈ _
      rw [N.same _ (by simpa using N.j_le)]
      exact Submodule.smul_mem _ _ hz
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_right
      (le_iSup₂_of_le (f := fun (a : Fin r) (_ : N.j ≤ a.val) => line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)) a ha le_rfl))

end Integers

theorem near_of_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∀ e : ℕ, 2 ≤ e → 𝔠 ^ e • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ Λ → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 → Λ ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 → ∃ s ∈ N.ZI, N.Near (𝔠 ^ (6 * e + 30)) (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT c hc0 hcs hcT hcD hsp n _ h1 _ _ h4
  obtain ⟨hNF, hL, hC, -, -, -, -, -, -, -, -, hPi⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.T.hermFramePair_ideal_kills_discriminantModules K V H hK r N g Λ hg hT c hc0 hcs hcT hcD
  obtain ⟨t, ht⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram K hK
  have hU : IsUnimod H Λ := hT.1.1
  let J := {b : Fin r // N.j ≤ b.val}
  let e : J → V := fun b => N.F.e b.1.castSucc
  let f : J → V := fun b => N.ist b.1
  have hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0 := fun a b => by
    simp only [e, f, N.ist_e a.1 b.1 b.2]
    exact if_congr Subtype.ext_iff.symm rfl rfl
  have heI : Submodule.span K (Set.range e) ≤ II N.F N.F' := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact e_mem_II N b.1 b.2
  have hII : II N.F N.F' ≤ V0 N.F N.F' := inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hV0 : ∀ x ∈ V0 N.F N.F', ∀ b, H.B x (e b) = 0 := fun x hx b =>
    (hNF.2.2.2.2.2.1 _ (e_mem_X _ b.1)).2 (e_mem_II N b.1 b.2) x hx
  have hWt : ∀ x ∈ N.Wt, ∀ b, H.B x (e b) = 0 := fun x hx b => by
    rw [← H.herm, hL.1 x hx _ (hII (e_mem_II N b.1 b.2)), star_zero]
  have hMf : ∀ y ∈ dualPart N, y ∈ Submodule.span K (Set.range f) := fun y hy => by
    have h : N.Ist ≤ Submodule.span K (Set.range f) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩
    exact h (dualPart_le N hy)
  have hMP : dualPart N ≤ N.P0 := le_sup_right
  have hst : StarSt K (⊤ : Ideal (𝓞 K)) := fun x _ => by
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (GlobalTheory.UnimodQuot.star_mem_one (Submodule.mem_one.2 ⟨x, rfl⟩))
    exact ⟨y, trivial, hy⟩
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx => by
    rw [← hU.2] at hx
    exact ((mem_dual_iff H Λ x).1 hx).2
  obtain ⟨Ψ, hΨ⟩ := exists_lift H hU hef (c • dualPart N) ((dualPart_fg N).of_le Submodule.smul_le_right)
    (fun y hy => hMf y (Submodule.smul_le_right hy)) (fun y hy x hx => by
      rw [← H.herm]
      exact star_one_mem hst (((mem_dual_iff H _ y).1 (k3 (Submodule.smul_mono le_rfl hMP hy))).2 x
        (h4 ⟨hx.1, heI hx.2⟩)))
  let π := N.Pi.projection N.Wt hC.symm
  have hlin : ∀ (L : V →ₗ[K] V) (a : 𝓞 K) v, L (a • v) = a • L v := fun L a v => by
    rw [← algebraMap_smul K a v, map_smul, algebraMap_smul]
  obtain ⟨s, hs1, hs2, hs3, hs4, hs5⟩ := core H e f hef (fun a b => N.F.iso _ _)
    (fun a b => N.ist_iso _ _ a.2 b.2) N.P0 (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) (dualPart N) Λ N.Pi
    (by rw [hPi, span_hermFramePair_lattice_eq_sup]) c hst hcs n t ht inf_le_left hMP (hermFramePair_lattice_decomposes_dualSpanPart N) (fun x hx => hV0 x hx.2) hMf
    (fun b => by rw [hPi]; exact Submodule.mem_sup_left (hII (e_mem_II N b.1 b.2))) (smul_le_iff.1 h1) hint k2 k3
    (π ∘ₗ Ψ) (fun y _ => Submodule.projection_apply_mem hC.symm _) (fun y hy b => by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc0
      have h := (hΨ _ (Submodule.smul_mem_smul ha hy)).2 b
      rw [hlin, ← smul_sub, B_smul, Algebra.smul_def, mul_eq_zero] at h
      have h' := h.resolve_left (by simpa using ha0)
      have h2 := hWt _ (Submodule.sub_projection_mem hC.symm (Ψ y)) b
      have e1 : (π ∘ₗ Ψ) y - y = (Ψ y - y) - (Ψ y - π (Ψ y)) := by
        rw [LinearMap.comp_apply]; abel
      rw [e1, map_sub, LinearMap.sub_apply, h', h2, sub_self])
    (fun y hy => by
      refine bd_add (n := 1) (m := 3) fun a ha => ?_
      rw [pow_one] at ha
      rw [← hlin]
      exact lift_bd N hU hL hsp k1 (hΨ _ (Submodule.smul_mem_smul ha hy)).1
        (Submodule.projection_apply_mem hC.symm _) (Submodule.sub_projection_mem hC.symm _))
  have hsI : ∀ v, s v - v ∈ II N.F N.F' := fun v => by
    rw [← neg_sub]; exact Submodule.neg_mem _ (heI (hs2 v))
  refine ⟨s, ⟨⟨Subgroup.subset_closure ⟨⟨hs1, s.bijective, fun a => ?_, fun y _ => (hsI y).1⟩,
    ⟨hs1, s.bijective, fun a => ?_, fun y _ => (hsI y).2⟩⟩, ?_⟩, ?_⟩, ?_, ?_⟩
  · have := hs3 _ (hV0 _ (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X N.F a))))
    simp [this]
  · have := hs3 _ (hV0 _ (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X N.F' a))))
    simp [this]
  · exact (mem_fixingSubgroup_iff _).2 fun y hy => hs3 y (hV0 y hy)
  · exact (mem_fixingSubgroup_iff _).2 fun y hy => hs3 y (hWt y hy)
  · refine le_inf (smul_le_iff.2 fun x hx => bd_mono (hs4 x hx) (by omega)) (Submodule.smul_le_right.trans ?_)
    intro x hx
    show x ∈ N.Pi
    rw [hPi, ← span_hermFramePair_lattice_eq_sup]
    exact Submodule.subset_span hx
  · exact smul_le_iff.2 fun x hx => bd_mono (hs5 x hx.1 hx.2) (by omega)

end GlobalTheory.DegCnt.DualPos
end
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∀ e : ℕ, 2 ≤ e → 𝔠 ^ e • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ Λ → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 → Λ ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 → ∃ s ∈ N.ZI, N.Near (𝔠 ^ (6 * e + 30)) (s • Λ) := by
  atlas_forward_decl GlobalTheory.DegCnt.DualPos.near_of_skew
end

section
section
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.NormalPos

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem mem_smul_iff (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (y : V) :
    y ∈ s • Λ ↔ ∃ x ∈ Λ, s x = y := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  rfl

theorem smul_inf_eq (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (S : Submodule K V)
    (h : ∀ y ∈ S, s y = y) : (s • Λ) ⊓ rs (𝓞 K) S = Λ ⊓ rs (𝓞 K) S := by
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hy⟩
    have : x = y := s.injective (hxy.trans (h y hy).symm)
    exact ⟨this ▸ hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨y, hx, h y hy⟩, hy⟩

theorem line_le (A : Submodule (𝓞 K) K) (v : V) (S : Submodule K V) (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t hv

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_II (N : NF H r) (a : Fin r) (ha : N.j ≤ a.val) : N.F.e a.castSucc ∈ II N.F N.F' := by
  have hc : N.c ≠ 0 := by
    intro h
    have := N.c_norm
    rw [h, zero_mul] at this
    exact zero_ne_one this
  refine ⟨Submodule.subset_span ⟨a, a.2, rfl⟩, ?_⟩
  have h1 : N.F'.e a.castSucc ∈ N.F'.X := Submodule.subset_span ⟨a, a.2, rfl⟩
  have h2 := N.F'.X.smul_mem N.c⁻¹ h1
  rwa [N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isotropicMeet_le_jointSpan (N : NF H r) : II N.F N.F' ≤ V0 N.F N.F' :=
  inf_le_left.trans (le_sup_left.trans le_sup_left)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem eq_zero_of_mem (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F')
    (d : V) (hd : d ∈ N.Ist) (hd' : d ∈ V0 N.F N.F') : d = 0 := by
  let φ : V →ₗ[K] V := ∑ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val),
    (H.B.flip (N.F.e a.castSucc)).smulRight (N.ist a)
  have h1 : N.Ist ≤ LinearMap.eqLocus φ LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : N.j ≤ b.val := hb
    show φ (N.ist b) = N.ist b
    simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
    rw [Finset.sum_eq_single b]
    · rw [← H.herm, N.ist_e b b hb']; simp
    · intro a _ hab
      rw [← H.herm, N.ist_e a b hb']; simp [hab]
    · intro h; exact absurd (by simpa using hb') h
  have h2 : φ d = d := h1 hd
  rw [← h2]
  simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  have ha' : N.j ≤ a.val := by simpa using ha
  have he := e_mem_II N a ha'
  rw [← H.herm, (hrad _ (isotropicMeet_le_jointSpan N he)).2 he d hd']
  simp

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_le_X (F : FlagD H r) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

theorem P0_inf_V0_le_sup_of_radical (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F') :
    N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') ≤ (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z := by
  set Q := (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z with hQ
  have hQV : Q ≤ rs (𝓞 K) (V0 N.F N.F') := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F N.j).trans (le_sup_left.trans le_sup_left) : N.F.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F' N.j).trans (le_sup_right.trans le_sup_left) : N.F'.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx => isotropicMeet_le_jointSpan N hx
    · exact line_le _ _ _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hP : N.P0 ≤ Q ⊔ rs (𝓞 K) N.Ist := by
    refine sup_le (le_sup_of_le_left (sup_le (sup_le ?_ ?_) le_sup_right)) (le_sup_of_le_right ?_)
    · refine iSup_le fun a => ?_
      have h0 : line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a)))
      by_cases ha : a.val < N.j
      · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
      · exact le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (e_mem_II N a (not_lt.1 ha)))))
    · refine iSup₂_le fun a ha => ?_
      have h0 : line (N.aa a) (N.F'.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_iSup₂ (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha)))
      exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
    · exact iSup₂_le fun a ha => line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  rintro p ⟨hp, hpV⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hP hp)
  have hdV : d ∈ V0 N.F N.F' := by
    have := (V0 N.F N.F').sub_mem hpV (hQV hu)
    rwa [add_sub_cancel_left] at this
  rw [eq_zero_of_mem N hrad d hd hdV, add_zero]
  exact hu

theorem fix_of_mem_Rs (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) : ∀ y ∈ N.Wt, s y = y :=
  fun y hy => (mem_fixingSubgroup_iff _).1 hs.2 y hy

theorem split_smul (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) {Λ : Submodule (𝓞 K) V}
    (hT : latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ) (h : N.Split Λ) : N.Split (s • Λ) := by
  unfold NF.Split at h ⊢
  rw [hT, smul_inf_eq s Λ _ (fix_of_mem_Rs N hs), h]

theorem near_mono (N : NF H r) {𝔞 𝔟 : Ideal (𝓞 K)} (h : 𝔞 ≤ 𝔟) {Λ : Submodule (𝓞 K) V}
    (hn : N.Near 𝔟 Λ) : N.Near 𝔞 Λ :=
  ⟨(Submodule.smul_mono_left h).trans hn.1, (Submodule.smul_mono_left h).trans hn.2⟩

end

theorem exists_near : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD hS
  have hrad := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1.2.2.2.1
  obtain ⟨s₁, hs₁, -, h₁⟩ := GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser K V H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h₁ _ rfl
  obtain ⟨t₁, -, th₁, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ hg hΛ s₁ hs₁.1
  have hS₁ := split_smul N hs₁ th₁ hS
  obtain ⟨s₂, hs₂, hfix, h₂⟩ := GlobalTheory.T.normal_form_ideal_divisibility K V H hK r N g _ hg t₁ 𝔠 h0 hst hT hD
  obtain ⟨b₁, b₂, b₃⟩ := h₂ _ rfl
  obtain ⟨t₂, -, th₂, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₁ s₂ hs₂.1
  have hS₂ := split_smul N hs₂ th₂ hS₁
  have e₁ := smul_inf_eq s₂ (s₁ • Λ) (N.F.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_left hy)
  have e₂ := smul_inf_eq s₂ (s₁ • Λ) (N.F'.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_right hy)
  have key : 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ s₂ • s₁ • Λ := by
    refine (smul_mono_right _ (P0_inf_V0_le_sup_of_radical N hrad)).trans ?_
    rw [Submodule.smul_sup, Submodule.smul_sup, Submodule.smul_sup]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine le_trans ?_ (e₁.ge.trans inf_le_left)
      exact le_inf a₁ (Submodule.smul_le_right.trans inf_le_right)
    · refine le_trans ?_ (e₂.ge.trans inf_le_left)
      exact le_inf a₂ (Submodule.smul_le_right.trans inf_le_right)
    · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))).trans b₁
    · exact (Submodule.smul_mono_left (Ideal.pow_le_self (by omega))).trans b₃
  obtain ⟨s₃, hs₃, hn⟩ := GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew K V H hK r N g _ hg t₂ 𝔠 h0 hst hT hD hS₂ (2 * r + 2) (by omega)
    key (by rw [e₁]; exact a₃) (by rw [e₂]; exact a₄) b₂
  have hs₃' : s₃ ∈ N.Rs := ⟨hs₃.1.1, hs₃.2⟩
  obtain ⟨-, -, th₃, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₂ s₃ hs₃'.1
  refine ⟨s₃ * (s₂ * s₁), N.Rs.mul_mem hs₃' (N.Rs.mul_mem hs₂ hs₁), ?_, ?_⟩
  · rw [mul_smul, mul_smul]
    exact split_smul N hs₃' th₃ hS₂
  · rw [mul_smul, mul_smul]
    exact near_mono N (Ideal.pow_le_pow_right (by omega)) hn

end GlobalTheory.DegCnt.NormalPos
end
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_exists_conj_near_reference : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  atlas_forward_decl GlobalTheory.DegCnt.NormalPos.exists_near
end
