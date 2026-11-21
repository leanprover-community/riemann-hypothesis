import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMargin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsHermiteReducedLatticeBasis

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DefForm

variable {E : Type} [Field E] [NumberField E]

def coordForm (m : ℕ) : (Fin m → 𝓞 E) →ₗ[ℤ] (Fin m → 𝓞 E) →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun y z => ∑ k, ∑ τ : E →+* ℂ, (τ (y k : E) * conj (τ (z k : E))).re)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, mul_assoc])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intro n y z; simp only [Finset.smul_sum, Pi.smul_apply]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; rw [zsmul_eq_mul, zsmul_eq_mul]; simp [mul_left_comm])

theorem sum_sum_mul_re {ι : Type} [Fintype ι] (c : ι → ℝ) (u : ι → ℂ) :
    ∑ a, ∑ b, c a * c b * (u a * conj (u b)).re = Complex.normSq (∑ a, (c a : ℂ) * u a) := by
  rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_ofReal,
    show (c a : ℂ) * u a * ((c b : ℂ) * conj (u b)) = ((c a * c b : ℝ) : ℂ) * (u a * conj (u b)) by push_cast; ring,
    Complex.re_ofReal_mul]

theorem coordForm_mem [IsCMField E] (H : Host E) (m : ℕ) : coordForm (E := E) m ∈ realForms H.bar (Fin m → 𝓞 E) := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · simp only [coordForm, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  · simp only [coordForm, LinearMap.mk₂_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    push_cast
    simp only [H.bar_eq, IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
    ring_nf

theorem coordForm_posDef (m : ℕ) : IsPosDef (coordForm (E := E) m) := by
  classical
  rw [isPosDef_iff_basis (Pi.basis fun _ : Fin m => RingOfIntegers.basis E)]
  intro c hc
  have hw : ∀ k (τ : E →+* ℂ), ∑ a, (c a : ℂ) * τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) =
      ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) := by
    intro k τ
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · exact Finset.sum_congr rfl fun j _ => by simp [Pi.basis_apply]
    · intro k' _ hk'
      exact Finset.sum_eq_zero fun j _ => by simp [Pi.basis_apply, Pi.single_apply, Ne.symm hk']
    · simp
  have hsum : ∑ a, ∑ a', c a * c a' * coordForm m ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a)
      ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a') =
      ∑ k, ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) := by
    simp_rw [← hw, ← sum_sum_mul_re]
    simp only [coordForm, LinearMap.mk₂_apply, Finset.mul_sum]
    calc _ = ∑ a, ∑ k, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ τ : E →+* ℂ, ∑ a', c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hsum]
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => hc ?_
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
  ext ⟨k, j⟩
  have h2 : ∀ τ : E →+* ℂ, ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) = 0 := fun τ =>
    Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1
      (h1 k (Finset.mem_univ _)) τ (Finset.mem_univ _))
  have h3 : ∑ j, (c ⟨k, j⟩ : ℂ) • canonicalEmbedding.latticeBasis E j = 0 := by
    ext τ
    simpa [canonicalEmbedding.latticeBasis_apply, integralBasis_apply, canonicalEmbedding.apply_at] using h2 τ
  have := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent _ h3 j
  simpa using this

theorem exists_posDef_realForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) X
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := f) fun x => LinearMap.congr_fun hs x
  refine ⟨pullR s (coordForm m), ⟨fun y z => (coordForm_mem H m).1 _ _, fun a y z => ?_⟩, ?_⟩
  · simp only [pullR_apply, map_smul]
    exact (coordForm_mem H m).2 a _ _
  · intro n x hx c hc
    exact coordForm_posDef m n (s ∘ x) (hx.map' s.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)) c hc

end GlobalTheory.DefForm
end
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_balanced_realForm_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  atlas_forward_decl GlobalTheory.DefForm.exists_posDef_realForm
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

open Filter Topology

namespace GlobalTheory.ConeSq

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def sq (l : ι → ℤ) : Matrix ι ι ℝ := vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))

def cone (S : Finset (ι → ℤ)) : Set (Matrix ι ι ℝ) :=
  {P | ∃ c : (ι → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • sq l}

theorem zero_mem (S : Finset (ι → ℤ)) : (0 : Matrix ι ι ℝ) ∈ cone S :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem add_mem {S : Finset (ι → ℤ)} {P Q : Matrix ι ι ℝ} (hP : P ∈ cone S) (hQ : Q ∈ cone S) :
    P + Q ∈ cone S := by
  obtain ⟨c, hc, rfl⟩ := hP
  obtain ⟨d, hd, rfl⟩ := hQ
  exact ⟨c + d, fun l => add_nonneg (hc l) (hd l), by simp [add_smul, Finset.sum_add_distrib]⟩

theorem smul_mem {S : Finset (ι → ℤ)} {P : Matrix ι ι ℝ} {a : ℝ} (ha : 0 ≤ a) (hP : P ∈ cone S) :
    a • P ∈ cone S := by
  obtain ⟨c, hc, rfl⟩ := hP
  exact ⟨a • c, fun l => mul_nonneg ha (hc l), by simp [Finset.smul_sum, smul_smul]⟩

theorem mono {S T : Finset (ι → ℤ)} (h : S ⊆ T) {P : Matrix ι ι ℝ} (hP : P ∈ cone S) :
    P ∈ cone T := by
  obtain ⟨c, hc, rfl⟩ := hP
  refine ⟨fun l => if l ∈ S then c l else 0, fun l => by dsimp only; split_ifs <;> simp [hc], ?_⟩
  rw [← Finset.sum_subset h (fun l _ hl => by simp [hl])]
  exact Finset.sum_congr rfl fun l hl => by simp [hl]

theorem sq_mem {S : Finset (ι → ℤ)} {l : ι → ℤ} (hl : l ∈ S) : sq l ∈ cone S := by
  refine ⟨fun m => if m = l then 1 else 0, fun m => by dsimp only; split_ifs <;> norm_num, ?_⟩
  rw [Finset.sum_eq_single l (fun m _ hm => by simp [hm]) (fun h => absurd hl h)]
  simp

theorem sum_mem {S : Finset (ι → ℤ)} {κ : Type} (s : Finset κ) {f : κ → Matrix ι ι ℝ}
    (h : ∀ k ∈ s, f k ∈ cone S) : ∑ k ∈ s, f k ∈ cone S :=
  Finset.sum_induction f (· ∈ cone S) (fun _ _ => add_mem) (zero_mem S) h

def plus (i j : ι) : ι → ℤ := Pi.single i 1 + Pi.single j 1

def minus (i j : ι) : ι → ℤ := Pi.single i 1 - Pi.single j 1

def gens : Finset (ι → ℤ) :=
  Finset.univ.image (fun p : ι × ι => plus p.1 p.2) ∪ Finset.univ.image (fun p : ι × ι => minus p.1 p.2)

def bsum : Matrix ι ι ℝ := ∑ p : ι × ι, (sq (plus p.1 p.2) + sq (minus p.1 p.2))

theorem sq_plus_sub_sq_minus (i j a b : ι) :
    sq (plus i j) a b - sq (minus i j) a b =
      2 * ((if a = i ∧ b = j then 1 else 0) + (if a = j ∧ b = i then 1 else 0)) := by
  simp only [sq, plus, minus, vecMulVec_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply,
    Int.cast_add, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rcases eq_or_ne i j with rfl | hij
  · by_cases h1 : a = i <;> by_cases h3 : b = i <;> simp [h1, h3] <;> norm_num
  · by_cases h1 : a = i <;> by_cases h2 : a = j <;> by_cases h3 : b = i <;> by_cases h4 : b = j <;>
      first
      | exact absurd (h1.symm.trans h2) hij
      | exact absurd (h3.symm.trans h4) hij
      | (simp [h1, h2, h3, h4, hij, hij.symm]; try norm_num)

theorem eq_sum_sq_sub (M : Matrix ι ι ℝ) (hM : ∀ a b, M a b = M b a) :
    M = ∑ p : ι × ι, (M p.1 p.2 / 4) • (sq (plus p.1 p.2) - sq (minus p.1 p.2)) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, sq_plus_sub_sq_minus]
  rw [Fintype.sum_prod_type]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [hM b a]; ring

theorem shift_mem (t : ℝ) (M : Matrix ι ι ℝ) (hM : ∀ a b, M a b = M b a)
    (hb : ∀ a b, |M a b| ≤ 4 * t) : t • bsum + M ∈ cone gens := by
  have e : t • bsum + M = ∑ p : ι × ι, ((t + M p.1 p.2 / 4) • sq (plus p.1 p.2)
      + (t - M p.1 p.2 / 4) • sq (minus p.1 p.2)) := by
    conv_lhs => rw [eq_sum_sq_sub M hM]
    rw [bsum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    module
  rw [e]
  refine sum_mem _ fun p _ => add_mem (smul_mem ?_ (sq_mem ?_)) (smul_mem ?_ (sq_mem ?_))
  · have := abs_le.mp (hb p.1 p.2); linarith
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  · have := abs_le.mp (hb p.1 p.2); linarith
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))

theorem sq_symm (l : ι → ℤ) (a b : ι) : sq l a b = sq l b a := by
  simp only [sq, vecMulVec_apply, mul_comm]

theorem bsum_symm (a b : ι) : (bsum : Matrix ι ι ℝ) a b = bsum b a := by
  simp only [bsum, Matrix.sum_apply, Matrix.add_apply]
  exact Finset.sum_congr rfl fun p _ => by rw [sq_symm _ a b, sq_symm (minus p.1 p.2) a b]

theorem quad_eq (M : Matrix ι ι ℝ) (c : ι → ℝ) :
    star c ⬝ᵥ (M *ᵥ c) = ∑ i, ∑ j, c i * c j * M i j := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tendsto_floor_div (x : ℝ) :
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) * x⌋ : ℤ) : ℝ) / N) atTop (𝓝 x) := by
  have h1 : Tendsto (fun N : ℕ => x - 1 / (N : ℝ)) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']
    have := Int.lt_floor_add_one ((N : ℝ) * x)
    linarith [mul_comm x (N : ℝ)]
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [div_le_iff₀ hN']
    have := Int.floor_le ((N : ℝ) * x)
    linarith [mul_comm x (N : ℝ)]

open scoped MatrixOrder in

theorem local_step (P₀ : Matrix ι ι ℝ) (h : P₀.PosDef) :
    ∃ S : Finset (ι → ℤ), ∀ᶠ P in 𝓝 P₀, P.IsHermitian → P ∈ cone S := by
  have hP₀s : ∀ a b, P₀ a b = P₀ b a := fun a b => by
    have := h.isHermitian.apply a b
    rw [star_trivial] at this
    exact this.symm
  obtain ⟨η, hη, hmar⟩ := GlobalTheory.posDef_quad_margin (fun i j => P₀ i j) (fun c hc => by
    have := h.dotProduct_mulVec_pos hc
    rwa [quad_eq] at this)
  set β : ℝ := ∑ a, ∑ b, |(bsum : Matrix ι ι ℝ) a b| + 1 with hβdef
  have hβ : 0 < β := by positivity
  have hbβ : ∀ a b, |(bsum : Matrix ι ι ℝ) a b| ≤ β := fun a b => by
    have h1 : |(bsum : Matrix ι ι ℝ) a b| ≤ ∑ b', |(bsum : Matrix ι ι ℝ) a b'| :=
      Finset.single_le_sum (f := fun b' => |(bsum : Matrix ι ι ℝ) a b'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : ∑ b', |(bsum : Matrix ι ι ℝ) a b'| ≤ ∑ a', ∑ b', |(bsum : Matrix ι ι ℝ) a' b'| :=
      Finset.single_le_sum (f := fun a' => ∑ b', |(bsum : Matrix ι ι ℝ) a' b'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  set t : ℝ := η / (2 * β) with htdef
  have ht : 0 < t := by positivity
  set G : Matrix ι ι ℝ := P₀ - (2 * t) • bsum with hGdef
  have hGs : ∀ a b, G a b = G b a := fun a b => by
    simp only [hGdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hP₀s a b, bsum_symm a b]
  have hG : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨IsHermitian.ext fun a b => by rw [star_trivial, hGs], fun c => ?_⟩
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    rw [quad_eq]
    have := hmar (fun a b => -(2 * t) * bsum a b) (fun a b => by
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      calc 2 * t * |(bsum : Matrix ι ι ℝ) a b| ≤ 2 * t * β := by gcongr; exact hbβ a b
        _ = η := by rw [htdef]; field_simp) c hc
    refine this.le.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    simp only [hGdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  set R : Matrix ι ι ℝ := CFC.sqrt G with hRdef
  have hR : R.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hRR : R * R = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  have hRs : ∀ a b, R a b = R b a := fun a b => by
    have := hR.isHermitian.apply a b
    rw [star_trivial] at this
    exact this.symm
  have hGsum : ∀ a b, G a b = ∑ k, R k a * R k b := fun a b => by
    rw [← hRR, mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hRs a k]
  have hconv : ∀ a b, Tendsto (fun N : ℕ => ∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N)) atTop (𝓝 (G a b)) := fun a b => by
    rw [hGsum]
    exact tendsto_finset_sum _ fun k _ => (tendsto_floor_div _).mul (tendsto_floor_div _)
  have hev : ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ a b, |∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N) - G a b| < t :=
    (eventually_gt_atTop 0).and (eventually_all.2 fun a => eventually_all.2 fun b =>
      (hconv a b).eventually (eventually_abs_sub_lt _ ht))
  obtain ⟨N, hN, hNt⟩ := hev.exists
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set m : ι → ι → ℤ := fun k a => ⌊(N : ℝ) * R k a⌋ with hmdef
  set Q : Matrix ι ι ℝ := ∑ k, (1 / (N : ℝ) ^ 2) • sq (m k) with hQdef
  have hQ : ∀ a b, Q a b = ∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N) := fun a b => by
    simp only [hQdef, hmdef, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sq, vecMulVec_apply]
    exact Finset.sum_congr rfl fun k _ => by field_simp
  have hQs : ∀ a b, Q a b = Q b a := fun a b => by
    rw [hQ, hQ]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hQmem : Q ∈ cone (Finset.univ.image m) :=
    sum_mem _ fun k _ => smul_mem (by positivity) (sq_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  refine ⟨gens ∪ Finset.univ.image m, ?_⟩
  have hnear : ∀ᶠ P in 𝓝 P₀, ∀ a b, |P a b - P₀ a b| < t :=
    eventually_all.2 fun a => eventually_all.2 fun b =>
      ((continuous_id.matrix_elem a b).tendsto P₀).eventually (eventually_abs_sub_lt _ ht)
  filter_upwards [hnear] with P hP hPh
  have hPs : ∀ a b, P a b = P b a := fun a b => by
    have := hPh.apply a b
    rw [star_trivial] at this
    exact this.symm
  set M : Matrix ι ι ℝ := (P - P₀) + (G - Q) with hMdef
  have e : P = Q + ((2 * t) • bsum + M) := by
    rw [hMdef, hGdef]; abel
  rw [e]
  refine add_mem (mono Finset.subset_union_right hQmem)
    (mono Finset.subset_union_left (shift_mem _ M ?_ ?_))
  · intro a b
    simp only [hMdef, Matrix.add_apply, Matrix.sub_apply]
    rw [hPs a b, hP₀s a b, hGs a b, hQs a b]
  · intro a b
    have h1 := hP a b
    have h2 := hNt a b
    rw [← hQ] at h2
    simp only [hMdef, Matrix.add_apply, Matrix.sub_apply]
    have h3 := abs_add_le (P a b - P₀ a b) (G a b - Q a b)
    rw [abs_sub_comm (G a b)] at h3
    linarith

theorem exists_finset_cone : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (𝒦 : Set (Matrix ι ι ℝ)),
    IsCompact 𝒦 → (∀ P ∈ 𝒦, P.PosDef) → ∃ S : Finset (ι → ℤ), ∀ P ∈ 𝒦, ∃ c : (ι → ℤ) → ℝ,
      (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  intro ι _ _ 𝒦 hK hpd
  choose S hS using fun P (hP : P ∈ 𝒦) => local_step P (hpd P hP)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover'
    (fun P hP => {Q : Matrix ι ι ℝ | Q.IsHermitian → Q ∈ cone (S P hP)}) hS
  refine ⟨t.biUnion (fun x => S x.1 x.2), fun P hP => ?_⟩
  obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.mp (ht hP)
  exact mono (Finset.subset_biUnion_of_mem _ hx) (hPx (hpd P hP).isHermitian)

end GlobalTheory.ConeSq
end
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (𝒦 : Set (Matrix ι ι ℝ)), IsCompact 𝒦 → (∀ P ∈ 𝒦, P.PosDef) → ∃ S : Finset (ι → ℤ), ∀ P ∈ 𝒦, ∃ c : (ι → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  atlas_forward_decl GlobalTheory.ConeSq.exists_finset_cone
end

section
open Matrix GlobalTheory.RedTh

noncomputable section

namespace GlobalTheory.SiegelCone

abbrev Tail {n : ℕ} (k : Fin n) : Type := {i : Fin n // k ≤ i}

def unip (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
    if i = j then {1} else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)

theorem isCompact_unip (n : ℕ) : IsCompact (unip n) := by
  refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_singleton
  · exact isCompact_Icc

theorem mem_unip {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : GlobalTheory.RedTh.IsSiegel d u) :
    u ∈ unip n := by
  intro i _ j _
  simp only
  split_ifs with h1 h2
  · subst h1; simp [h.diag]
  · simp [h.lower i j h2]
  · have : i < j := lt_of_le_of_ne (not_lt.1 h2) h1
    exact abs_le.1 (h.upper i j this)

def tailForm {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Tail k) (Tail k) ℝ :=
  (u.submatrix Subtype.val Subtype.val)ᵀ * diagonal (fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹) *
    u.submatrix Subtype.val Subtype.val

theorem continuous_tailForm {n : ℕ} (k : Fin n) : Continuous (tailForm k) := by
  unfold tailForm
  exact ((continuous_id.matrix_submatrix _ _).matrix_transpose.matrix_mul continuous_const).matrix_mul
    (continuous_id.matrix_submatrix _ _)

theorem tailForm_posDef {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) :
    (tailForm k u).PosDef := by
  have hu' : ∀ i j, u i j ∈ (if i = j then ({1} : Set ℝ) else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)) :=
    fun i j => hu i trivial j trivial
  set v := u.submatrix (Subtype.val : Tail k → Fin n) Subtype.val
  have htri : v.BlockTriangular id := by
    intro a b hab
    have := hu' a.1 b.1
    have hne : a.1 ≠ b.1 := fun h => (ne_of_lt hab) (Subtype.ext h).symm
    simp only [hne, if_false, show b.1 < a.1 from hab, if_true, Set.mem_singleton_iff] at this
    exact this
  have hdet : v.det = 1 := by
    rw [det_of_upperTriangular htri]
    refine Finset.prod_eq_one fun a _ => ?_
    have := hu' a.1 a.1
    simpa [v] using this
  have hunit : IsUnit v := (isUnit_iff_isUnit_det v).2 (by rw [hdet]; exact isUnit_one)
  have hD : (diagonal fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹).PosDef :=
    posDef_diagonal_iff.2 fun a => by positivity
  have := hD.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hunit)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this

theorem tailForm_apply {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) (a b : Tail k) :
    tailForm k u a b = ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m a.1 * u m b.1 else 0 := by
  rw [tailForm, mul_apply]
  simp only [mul_diagonal, transpose_apply, submatrix_apply]
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (k ≤ ·)) (p := (k ≤ ·)) (by simp)]
  refine Finset.sum_congr rfl fun c _ => by ring

end GlobalTheory.SiegelCone

namespace GlobalTheory.SiegelCone

def extZ {n : ℕ} (k : Fin n) (l : Tail k → ℤ) : Fin n → ℤ := fun i => if h : k ≤ i then l ⟨i, h⟩ else 0

theorem exists_increments {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hs : GlobalTheory.RedTh.IsSiegel d u) :
    ∃ G : Fin n → ℝ, (∀ k, 0 ≤ G k) ∧ ∀ m, d m = ((4 : ℝ) ^ (m : ℕ))⁻¹ * ∑ k, if k ≤ m then G k else 0 := by
  let F : ℕ → ℝ := fun m => if h : m < n then d ⟨m, h⟩ * 4 ^ m else 0
  let G : ℕ → ℝ := fun k => if k = 0 then F 0 else F k - F (k - 1)
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), G k = F m := by
    intro m
    induction m with
    | zero => simp [G]
    | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [G, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]; ring
  refine ⟨fun k => G k, fun k => ?_, fun m => ?_⟩
  · by_cases h0 : (k : ℕ) = 0
    · have := hs.nonneg k
      simp only [G, h0, if_true, F, dif_pos (show 0 < n from lt_of_le_of_lt (Nat.zero_le _) k.2)]
      have e : (⟨0, lt_of_le_of_lt (Nat.zero_le _) k.2⟩ : Fin n) = k := Fin.ext h0.symm
      rw [e]; positivity
    · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
      have hjn : j < n := by omega
      have hstep := hs.step ⟨j, hjn⟩ k (by simp [hj])
      have hnn := hs.nonneg ⟨j, hjn⟩
      have hdk : ∀ h, d ⟨j + 1, h⟩ = d k := fun h => congrArg d (Fin.ext hj.symm)
      have hFk : F (j + 1) = d k * 4 ^ (j + 1) := by
        simp only [F, dif_pos (show j + 1 < n by omega), hdk]
      have hFj : F j = d ⟨j, hjn⟩ * 4 ^ j := by simp only [F, dif_pos hjn]
      show 0 ≤ G (k : ℕ)
      rw [hj]
      simp only [G, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hFk, hFj, pow_succ]
      have : (0 : ℝ) ≤ 4 ^ j := by positivity
      nlinarith
  · have hsum : ∑ k : Fin n, (if k ≤ m then G k else 0) = F m := by
      have h1 : ∀ k : Fin n, (if k ≤ m then G k else 0) = (fun x : ℕ => if x ≤ (m : ℕ) then G x else 0) k :=
        fun k => by simp only [Fin.le_iff_val_le_val]
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Fin.sum_univ_eq_sum_range (fun x => if x ≤ (m : ℕ) then G x else 0) n,
        ← Finset.sum_filter]
      have h2 : (Finset.range n).filter (· ≤ (m : ℕ)) = Finset.range ((m : ℕ) + 1) := by
        ext x; simp; omega
      rw [h2, htel]
    rw [hsum]
    simp only [F, dif_pos m.2, Fin.eta]
    field_simp

theorem tail_sum {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) (T : Finset (Tail k → ℤ))
    (C : (Tail k → ℤ) → ℝ)
    (hC : tailForm k u = ∑ l ∈ T, C l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))) (i j : Fin n) :
    ∑ l ∈ T, C l * ((extZ k l i : ℝ) * (extZ k l j : ℝ)) =
      ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
  have hlow : ∀ m i, k ≤ m → ¬ k ≤ i → u m i = 0 := by
    intro m i hm hi
    have := hu m trivial i trivial
    have hlt : i < m := lt_of_lt_of_le (not_le.1 hi) hm
    simpa [hlt.ne', hlt] using this
  by_cases hi : k ≤ i
  · by_cases hj : k ≤ j
    · have := congrFun (congrFun hC ⟨i, hi⟩) ⟨j, hj⟩
      rw [tailForm_apply] at this
      rw [this]
      simp [Matrix.sum_apply, vecMulVec_apply, extZ, hi, hj]
    · simp only [extZ, dif_neg hj, Int.cast_zero, mul_zero]
      simp only [Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hm
      · rw [hlow m j hm hj, mul_zero]
      · rfl
  · simp only [extZ, dif_neg hi, Int.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    split_ifs with hm
    · rw [hlow m i hm hi, mul_zero, zero_mul]
    · rfl

theorem gram_mem_cone : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ),
    GlobalTheory.RedTh.IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧
      GlobalTheory.RedTh.gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  intro n
  have hK : ∀ k : Fin n, ∃ T : Finset (Tail k → ℤ), ∀ P ∈ tailForm k '' unip n, ∃ c : (Tail k → ℤ) → ℝ,
      (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ T, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := fun k =>
    GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef (Tail k) (tailForm k '' unip n) ((isCompact_unip n).image (continuous_tailForm k))
      (by rintro _ ⟨u, hu, rfl⟩; exact tailForm_posDef k hu)
  choose T hT using hK
  refine ⟨Finset.univ.biUnion fun k => (T k).image (extZ k), ?_⟩
  intro d u hs
  have hu := mem_unip hs
  choose C hC0 hC using fun k => hT k _ ⟨u, hu, rfl⟩
  obtain ⟨G, hG0, hd⟩ := exists_increments hs
  refine ⟨fun l => ∑ k : Fin n, G k * ∑ l' ∈ T k, if extZ k l' = l then C k l' else 0, fun l => ?_, ?_⟩
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (hG0 k) (Finset.sum_nonneg fun l' _ => ?_)
    split_ifs
    · exact hC0 k l'
    · exact le_rfl
  ext i j
  have hL : GlobalTheory.RedTh.gram d u i j = ∑ k, G k * ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
    calc GlobalTheory.RedTh.gram d u i j = ∑ m, u m i * d m * u m j := by
          rw [GlobalTheory.RedTh.gram, mul_apply]; simp only [mul_diagonal, transpose_apply]
      _ = ∑ m : Fin n, ∑ k : Fin n, if k ≤ m then G k * (((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j) else 0 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hd m, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          split_ifs <;> ring
  rw [hL]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp_rw [← tail_sum _ hu _ _ (hC _)]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' hl' => ?_
  have hmem : extZ k l' ∈ Finset.univ.biUnion fun k => (T k).image (extZ k) :=
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hl'⟩
  simp_rw [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]
  ring

end GlobalTheory.SiegelCone
end
end

section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelGram_mem_cone_integer_squares : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  first | exact @GlobalTheory.SiegelCone.gram_mem_cone | exact GlobalTheory.SiegelCone.gram_mem_cone | (intros; apply GlobalTheory.SiegelCone.gram_mem_cone <;> assumption)
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped MatrixOrder

namespace GlobalTheory.RedTh.RedBasis

theorem sum_sum_eq_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * G i j = c ⬝ᵥ (G *ᵥ c) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_transpose_mul_self {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hs : Gᵀ = G)
    (hp : ∀ c : Fin n → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * G i j) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ, g.det ≠ 0 ∧ gᵀ * g = G := by
  have hT : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · show Gᴴ = G
      rw [conjTranspose_eq_transpose_of_trivial, hs]
    · by_cases hx : x = 0
      · simp [hx]
      · have := (hp x hx).le
        rw [sum_sum_eq_dotProduct] at this
        simpa using this
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hT
  have hsq : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hsym : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsq.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hgG : (CFC.sqrt G)ᵀ * CFC.sqrt G = G := by
    rw [hsym, CFC.sqrt_mul_sqrt_self G h0]
  refine ⟨CFC.sqrt G, fun hd => ?_, hgG⟩
  obtain ⟨v, hv, hgv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h := hp v hv
  rw [sum_sum_eq_dotProduct, ← hgG, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hgv] at h
  simp at h

theorem exists_siegel_basis : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y)
    (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y)
    (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧
    ∀ i j, B (b i) (b j) = gram d u i j := by
  intro n Y _ b₀ B hs hB
  let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => B (b₀ i) (b₀ j)
  obtain ⟨g, hg, hgG⟩ := exists_transpose_mul_self G (by ext i j; simp [G, hs])
    (by simpa [G] using (isPosDef_iff_basis b₀ B).1 hB)
  obtain ⟨γ, k, a, m, hγ, hk, ha, h1, h0, hup, hstep, hdec⟩ :=
    GlobalTheory.ClassFin.HermiteReduction.exists_reduced n g hg
  have hu : IsUnit γ.det := by rcases hγ with h | h <;> rw [h] <;> simp
  let e : Y ≃ₗ[ℤ] Y := Matrix.toLinearEquiv b₀ γ hu
  have hbe : ∀ j, b₀.map e j = ∑ i, γ i j • b₀ i := fun j => by
    simp [e, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hM : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) = gram (fun i => a i ^ 2) m := by
    have e1 : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) =
        (g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ)) := by
      rw [← hgG, transpose_mul]; simp only [Matrix.mul_assoc]
    have e2 : (k * diagonal a * m)ᵀ * (k * diagonal a * m) = mᵀ * (diagonal a * (kᵀ * k) * diagonal a) * m := by
      simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hdec, e2, hk, Matrix.mul_one, diagonal_mul_diagonal, gram]
    simp only [sq]
  refine ⟨b₀.map e, fun i => a i ^ 2, m, ⟨fun i => sq_nonneg _, fun p q hq => ?_, h1, h0, hup⟩,
    fun i => pow_pos (ha i) 2, fun i j => ?_⟩
  · have h2 := hstep p q hq
    have h3 := ha p
    have h4 := ha q
    show a p ^ 2 ≤ 4 * a q ^ 2
    nlinarith
  · rw [← hM, hbe, hbe]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Matrix.mul_apply,
      transpose_apply, map_apply, G, of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.RedTh.RedBasis
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y) (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y) (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧ ∀ i j, B (b i) (b j) = gram d u i j := by
  atlas_forward_decl GlobalTheory.RedTh.RedBasis.exists_siegel_basis
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.RedTh

def siegelGlueMat {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (s + m)) (Fin (s + m)) ℝ := fun i j =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun y => a x y) (fun _ => 0) j)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun _ => 0) (fun y => b x y) j) i

@[simp] lemma siegelGlueMat_ll {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin s) : siegelGlueMat a b (Fin.castAdd m x) (Fin.castAdd m y) = a x y := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_lr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin s) (y : Fin m) : siegelGlueMat a b (Fin.castAdd m x) (Fin.natAdd s y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rl {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m) (y : Fin s) : siegelGlueMat a b (Fin.natAdd s x) (Fin.castAdd m y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m) : siegelGlueMat a b (Fin.natAdd s x) (Fin.natAdd s y) = b x y := by
  simp [siegelGlueMat]

lemma gram_apply_glue {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    gram d u i j = ∑ k, u k i * d k * u k j := by
  simp only [gram]
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

lemma siegelGlue_scale {s m : ℕ} (d₁ : Fin s → ℝ) (d₂ : Fin m → ℝ) (h₁ : ∀ i, 0 < d₁ i)
    (h₂ : ∀ i, 0 < d₂ i) :
    ∃ t : ℝ, 0 < t ∧ ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → t * d₁ i ≤ 4 * d₂ j := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨1, one_pos, fun _ j => j.elim0⟩
  · set j0 : Fin m := ⟨0, hm⟩
    have hS : 0 ≤ ∑ i, d₁ i := Finset.sum_nonneg (fun i _ => (h₁ i).le)
    refine ⟨d₂ j0 / (1 + ∑ i, d₁ i), div_pos (h₂ j0) (by linarith), fun i j hj => ?_⟩
    have hj' : j = j0 := Fin.ext hj
    subst hj'
    have hi : d₁ i ≤ ∑ k, d₁ k := Finset.single_le_sum (fun k _ => (h₁ k).le) (Finset.mem_univ i)
    have hpos : 0 < 1 + ∑ k, d₁ k := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have := h₂ j0
    nlinarith

lemma isSiegel_glue {s m : ℕ} {e₁ : Fin s → ℝ} {u₁ : Matrix (Fin s) (Fin s) ℝ} {e₂ : Fin m → ℝ}
    {u₂ : Matrix (Fin m) (Fin m) ℝ} (h₁ : IsSiegel e₁ u₁) (h₂ : IsSiegel e₂ u₂)
    (hj : ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → e₁ i ≤ 4 * e₂ j) :
    IsSiegel (Fin.append e₁ e₂) (siegelGlueMat u₁ u₂) where
  nonneg i := by
    induction i using Fin.addCases with
    | left a => simpa using h₁.nonneg a
    | right a => simpa using h₂.nonneg a
  step p q h := by
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd] at h
        simpa using h₁.step a b h
      | right b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := a.isLt
        simpa using hj a b (by omega)
    | right a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := b.isLt
        omega
      | right b =>
        simp only [Fin.val_natAdd] at h
        simpa using h₂.step a b (by omega)
  diag i := by
    induction i using Fin.addCases with
    | left a => simpa using h₁.diag a
    | right a => simpa using h₂.diag a
  lower i j h := by
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.lower a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.lower a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)
  upper i j h := by
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.upper a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.upper a b (by rw [Fin.lt_iff_val_lt_val] at h ⊢; simpa using h)

lemma isSiegel_zero_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u) :
    IsSiegel (0 : Fin n → ℝ) u where
  nonneg _ := le_refl _
  step _ _ _ := by simp
  diag := h.diag
  lower := h.lower
  upper := h.upper

lemma isSiegel_smul_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u)
    {t : ℝ} (ht : 0 ≤ t) : IsSiegel (fun i => t * d i) u where
  nonneg i := mul_nonneg ht (h.nonneg i)
  step p q hpq := by
    have := h.step p q hpq
    nlinarith
  diag := h.diag
  lower := h.lower
  upper := h.upper

theorem siegelData_glue_scaled : ∀ (s m : ℕ) (d₁ : Fin s → ℝ) (u₁ : Matrix (Fin s) (Fin s) ℝ) (d₂ : Fin m → ℝ) (u₂ : Matrix (Fin m) (Fin m) ℝ), IsSiegel d₁ u₁ → IsSiegel d₂ u₂ → (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → ∃ (t : ℝ) (d d' : Fin (s + m) → ℝ) (u : Matrix (Fin (s + m)) (Fin (s + m)) ℝ), 0 < t ∧ IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j : Fin s, gram d u (Fin.castAdd m i) (Fin.castAdd m j) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.castAdd m j) = t * gram d₁ u₁ i j) ∧ (∀ (i : Fin s) (j : Fin m), gram d u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d u (Fin.natAdd s j) (Fin.castAdd m i) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d' u (Fin.natAdd s j) (Fin.castAdd m i) = 0) ∧ ∀ i j : Fin m, gram d u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j ∧ gram d' u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j := by
  intro s m d₁ u₁ d₂ u₂ h₁ h₂ p₁ p₂
  obtain ⟨t, ht, hj⟩ := siegelGlue_scale d₁ d₂ p₁ p₂
  refine ⟨t, Fin.append (0 : Fin s → ℝ) d₂, Fin.append (fun i => t * d₁ i) d₂, siegelGlueMat u₁ u₂, ht,
    isSiegel_glue (isSiegel_zero_of h₁) h₂ (fun i j _ => by simpa using (h₂.nonneg j)),
    isSiegel_glue (isSiegel_smul_of h₁ ht.le) h₂ hj, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using mul_pos ht (p₁ a)
    | right a => simpa using p₂ a
  · intro i j
    refine ⟨?_, ?_⟩
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue, Finset.mul_sum]
      simp only [siegelGlueMat_ll, siegelGlueMat_rl, Fin.append_left, Fin.append_right, zero_mul,
        mul_zero, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
  · intro i j
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
  · intro i j
    refine ⟨?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue]
      simp

end GlobalTheory.RedTh
end
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_reduction_orthogonal : ∀ (s m : ℕ) (d₁ : Fin s → ℝ) (u₁ : Matrix (Fin s) (Fin s) ℝ) (d₂ : Fin m → ℝ) (u₂ : Matrix (Fin m) (Fin m) ℝ), IsSiegel d₁ u₁ → IsSiegel d₂ u₂ → (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → ∃ (t : ℝ) (d d' : Fin (s + m) → ℝ) (u : Matrix (Fin (s + m)) (Fin (s + m)) ℝ), 0 < t ∧ IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j : Fin s, gram d u (Fin.castAdd m i) (Fin.castAdd m j) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.castAdd m j) = t * gram d₁ u₁ i j) ∧ (∀ (i : Fin s) (j : Fin m), gram d u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d u (Fin.natAdd s j) (Fin.castAdd m i) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d' u (Fin.natAdd s j) (Fin.castAdd m i) = 0) ∧ ∀ i j : Fin m, gram d u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j ∧ gram d' u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j := by
  atlas_forward_decl GlobalTheory.RedTh.siegelData_glue_scaled
end

section
noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem exists_siegel_split {X X₁ : Type} [AddCommGroup X] [AddCommGroup X₁] [Module.Finite ℤ X] [Module.Free ℤ X]
    [Module.Finite ℤ X₁] [Module.Free ℤ X₁] (r : X →ₗ[ℤ] X₁) (σ : X₁ →ₗ[ℤ] X) (hrσ : ∀ y, r (σ y) = y)
    (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hs₀ : ∀ y z, B₀ y z = B₀ z y) (hp₀ : IsPosDef B₀)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (hs₁ : ∀ y z, B₁ y z = B₁ z y) (hp₁ : IsPosDef B₁)
    (n : ℕ) (hn : Module.finrank ℤ X = n) :
    ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (t : ℝ),
      IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j, B₁ (r (b i)) (r (b j)) = gram d u i j) ∧
      ∀ i j, t * B₀ (b i - σ (r (b i))) (b j - σ (r (b j))) + B₁ (r (b i)) (r (b j)) = gram d' u i j := by
  classical
  have hfree : Module.Free ℤ (LinearMap.ker r) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, ⟨bK⟩⟩ : ∃ s, Nonempty (Module.Basis (Fin s) ℤ (LinearMap.ker r)) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  obtain ⟨m, ⟨bQ⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℤ X₁) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  let BK : LinearMap.ker r →ₗ[ℤ] LinearMap.ker r →ₗ[ℤ] ℝ := B₀.compl₁₂ (LinearMap.ker r).subtype (LinearMap.ker r).subtype
  have hpK : IsPosDef BK := fun k x hx c hc =>
    hp₀ k (fun i => (x i : X)) (hx.map' (LinearMap.ker r).subtype (Submodule.ker_subtype _)) c hc
  obtain ⟨b₁, d₁, u₁, hS₁, hd₁, hg₁⟩ := GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form s _ bK BK (fun y z => hs₀ _ _) hpK
  obtain ⟨b₂, d₂, u₂, hS₂, hd₂, hg₂⟩ := GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form m _ bQ B₁ hs₁ hp₁
  obtain ⟨t, d, d', u, -, hS, hS', hd', g11, g12, g22⟩ := GlobalTheory.T.exists_siegel_reduction_orthogonal s m d₁ u₁ d₂ u₂ hS₁ hS₂ hd₁ hd₂
  let p : X →ₗ[ℤ] LinearMap.ker r := LinearMap.codRestrict _ (LinearMap.id - σ ∘ₗ r) fun x => by
    simp [hrσ]
  let e : X ≃ₗ[ℤ] LinearMap.ker r × X₁ := LinearEquiv.ofLinear (p.prod r) ((LinearMap.ker r).subtype.coprod σ)
    (by
      ext x
      · simp [p, LinearMap.mem_ker.1 x.2]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [p, hrσ]
      · simp [hrσ])
    (by ext x; simp [p])
  let c : Module.Basis (Fin (s + m)) ℤ X := ((b₁.prod b₂).map e.symm).reindex finSumFinEquiv
  have hc₁ : ∀ i, c (Fin.castAdd m i) = (b₁ i : X) := fun i => by
    have : finSumFinEquiv.symm (Fin.castAdd m i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
    simp [c, this, e]
  have hc₂ : ∀ j, c (Fin.natAdd s j) = σ (b₂ j) := fun j => by
    have : finSumFinEquiv.symm (Fin.natAdd s j) = Sum.inr j := finSumFinEquiv_symm_apply_natAdd j
    simp [c, this, e]
  have hnm : n = s + m := by
    rw [← hn, Module.finrank_eq_card_basis c, Fintype.card_fin]
  subst hnm
  have hr₁ : ∀ i, r (c (Fin.castAdd m i)) = 0 := fun i => by rw [hc₁]; exact (b₁ i).2
  have hr₂ : ∀ j, r (c (Fin.natAdd s j)) = b₂ j := fun j => by rw [hc₂, hrσ]
  have hq₁ : ∀ i, c (Fin.castAdd m i) - σ (r (c (Fin.castAdd m i))) = (b₁ i : X) := fun i => by
    rw [hr₁, map_zero, sub_zero, hc₁]
  have hq₂ : ∀ j, c (Fin.natAdd s j) - σ (r (c (Fin.natAdd s j))) = 0 := fun j => by rw [hr₂, hc₂, sub_self]
  refine ⟨c, d, d', u, t, hS, hS', hd', fun i j => ?_, fun i j => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [hr₁, (g11 _ _).1]
    · simp [hr₁, (g12 _ _).1]
    · simp [hr₁, (g12 _ _).2.1]
    · rw [hr₂, hr₂, hg₂, (g22 _ _).1]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [hq₁, hq₁, hr₁, hr₁, map_zero, add_zero, (g11 _ _).2, ← hg₁]
      rfl
    · rw [hq₁, hq₂, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.1.symm
    · rw [hq₂, hq₁, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.2.symm
    · rw [hq₂, hq₂, hr₂, hr₂]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, zero_add]
      rw [hg₂, (g22 _ _).2]

theorem projective_int_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module.Free ℤ O]
    [Module.Projective O M] : Module.Projective ℤ M := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective O M›
  let i : M →ₗ[ℤ] (M →₀ O) := s.toAddMonoidHom.toIntLinearMap
  let p : (M →₀ O) →ₗ[ℤ] M := (Finsupp.linearCombination O id).toAddMonoidHom.toIntLinearMap
  exact Module.Projective.of_split i p (LinearMap.ext fun x => LinearMap.congr_fun hs x)

theorem exists_adapted_siegel_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone H.bar X, ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  intro E _ _ _ H X _ _ _ _ B₀ hB₀ hp₀ n hn B hB
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Finite ℤ X₁ := Module.Finite.trans (𝓞 E) X₁
  have : Module.Projective ℤ X := projective_int_of_projective (O := 𝓞 E)
  have : Module.Projective ℤ X₁ := projective_int_of_projective (O := 𝓞 E)
  have : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have : Module.Free ℤ X₁ := Module.free_of_finite_type_torsion_free'
  let rZ : X →ₗ[ℤ] X₁ := r.toAddMonoidHom.toIntLinearMap
  let σZ : X₁ →ₗ[ℤ] X := σ.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, d, d', u, t, hS, hS', hd', hg, hg'⟩ := exists_siegel_split rZ σZ hrσ B₀ hB₀.1 hp₀ B₁ hB₁.1 hp₁ n hn
  let π : X →ₗ[𝓞 E] X := LinearMap.id - σ ∘ₗ r
  let πZ : X →ₗ[ℤ] X := π.toAddMonoidHom.toIntLinearMap
  refine ⟨b, d, d', u, t • B₀.compl₁₂ πZ πZ + B₁.compl₁₂ rZ rZ, hS, hS', hd', ⟨fun y z => ?_, fun a y z => ?_⟩,
    fun i j => (hBr _ _).trans (hg i j), fun i j => (hg' i j).symm ▸ ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply]
    rw [hB₀.1, hB₁.1]
  · have e₁ : ∀ y, πZ (a • y) = a • πZ y := fun y => π.map_smul a y
    have e₂ : ∀ y, rZ (a • y) = a • rZ y := fun y => r.map_smul a y
    have e₃ : ∀ y, πZ (H.bar a • y) = H.bar a • πZ y := fun y => π.map_smul _ y
    have e₄ : ∀ y, rZ (H.bar a • y) = H.bar a • rZ y := fun y => r.map_smul _ y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, e₁, e₂, e₃, e₄]
    rw [hB₀.2, hB₁.2]
  · rfl

end GlobalTheory.RedTh
end
end

section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone H.bar X, ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  first | exact @GlobalTheory.RedTh.exists_adapted_siegel_basis | exact GlobalTheory.RedTh.exists_adapted_siegel_basis | (intros; apply GlobalTheory.RedTh.exists_adapted_siegel_basis <;> assumption)
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem siegel_unipotent_inv_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  intro n
  refine ⟨(Nat.factorial n : ℝ), ?_⟩
  intro u hdiag hlow hup
  have hbt : u.BlockTriangular id := fun i j hij => hlow i j hij
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    simp [hdiag]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  refine ⟨u⁻¹, Matrix.nonsing_inv_mul u hunit, Matrix.mul_nonsing_inv u hunit, ?_, ?_⟩
  · intro i j hij
    letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
    exact Matrix.blockTriangular_inv_of_blockTriangular hbt hij
  · intro i j
    have hinv : u⁻¹ = u.adjugate := by
      rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have hb : ∀ a b, |(u.updateRow j (Pi.single i 1)) a b| ≤ 1 := by
      intro a b
      by_cases ha : a = j
      · subst ha
        rw [Matrix.updateRow_self]
        by_cases hb : b = i
        · subst hb; simp
        · simp [Pi.single_apply, hb]
      · rw [Matrix.updateRow_ne ha]
        rcases lt_trichotomy a b with h | h | h
        · linarith [hup a b h]
        · subst h; simp [hdiag]
        · simp [hlow a b h]
    have := Matrix.det_le (abv := AbsoluteValue.abs) hb
    simpa using this

end GlobalTheory
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnipotent_inverse_entries_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  atlas_forward_decl GlobalTheory.siegel_unipotent_inv_bounded
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem adjoint_weighted_sq_trace : ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (∀ p q, d p * (u * A.map (Int.cast : ℤ → ℝ) * v) p q = d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) q p) ∧ (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ)) ∧ ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ) := by
  intro n A A' d u v hd hvu huv h
  set a := A.map (Int.cast : ℤ → ℝ) with ha
  set a' := A'.map (Int.cast : ℤ → ℝ) with ha'
  have key : (u * a * v)ᵀ * diagonal d = diagonal d * (u * a' * v) := by
    have h2 := congrArg (fun M => vᵀ * M * v) h
    simp only [gram] at h2
    have e1 : vᵀ * (aᵀ * (uᵀ * diagonal d * u)) * v = (u * a * v)ᵀ * diagonal d * (u * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    have e2 : vᵀ * (uᵀ * diagonal d * u * a') * v = (u * v)ᵀ * diagonal d * (u * a' * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e1, e2, huv] at h2
    simpa using h2
  have c1 : ∀ p q, d p * (u * a * v) p q = d q * (u * a' * v) q p := by
    intro p q
    have := congrFun (congrFun key q) p
    simp only [mul_diagonal, diagonal_mul, transpose_apply] at this
    linarith
  have htr : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = (((A' * A).trace : ℤ) : ℝ) := by
    have e : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = ((u * a' * v) * (u * a * v)).trace := by
      rw [Finset.sum_comm]; simp [Matrix.trace, Matrix.mul_apply]
    rw [e]
    have : (u * a' * v) * (u * a * v) = u * (a' * a) * v := by
      rw [show (u * a' * v) * (u * a * v) = u * a' * (v * u) * a * v by simp only [Matrix.mul_assoc], hvu]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hvu, Matrix.one_mul]
    rw [ha, ha']
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply]
    push_cast; rfl
  refine ⟨c1, ?_, ?_⟩
  · rw [← htr]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hq := (hd q).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hq, sq, ← mul_assoc, c1 p q]; ring
  · rw [← htr, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hp := (hd p).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hp, sq, ← mul_assoc, ← c1 p q]; ring

end GlobalTheory.RedTh
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace : ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (∀ p q, d p * (u * A.map (Int.cast : ℤ → ℝ) * v) p q = d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) q p) ∧ (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ)) ∧ ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ) := by
  atlas_forward_decl GlobalTheory.RedTh.adjoint_weighted_sq_trace
end

section
namespace GlobalTheory.SiegelChain

theorem siegel_chain : ∀ {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ}, GlobalTheory.RedTh.IsSiegel d u →
    ∀ (m : ℕ) (i j : Fin n), (↑j : ℕ) = (↑i : ℕ) + m → d i ≤ (4 : ℝ) ^ m * d j := by
  intro n d u h m
  induction m with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by simpa using hij.symm)
    subst this
    simp
  | succ m ih =>
    intro i j hij
    have hk : (i : ℕ) + m < n := by have := j.isLt; omega
    let k : Fin n := ⟨(i : ℕ) + m, hk⟩
    have h1 : d i ≤ 4 ^ m * d k := ih i k rfl
    have h2 : d k ≤ 4 * d j := h.step k j (by simp [k]; omega)
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    calc d i ≤ 4 ^ m * d k := h1
      _ ≤ 4 ^ m * (4 * d j) := mul_le_mul_of_nonneg_left h2 h4
      _ = 4 ^ (m + 1) * d j := by ring

end GlobalTheory.SiegelChain
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SiegelGap

theorem chain {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u) :
    ∀ m : ℕ, ∀ i j : Fin n, (j : ℕ) = i + m → d i ≤ 4 ^ m * d j := by
  first
  | exact @_root_.GlobalTheory.SiegelChain.siegel_chain
  | exact _root_.GlobalTheory.SiegelChain.siegel_chain
  | (apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SiegelChain.siegel_chain <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SiegelChain.siegel_chain ..)

theorem chain_le {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u)
    (i j : Fin n) (h : i ≤ j) : d i ≤ 4 ^ n * d j := by
  have h1 := chain hS ((j : ℕ) - i) i j (by have : (i:ℕ) ≤ j := h; omega)
  have hm : (4:ℝ) ^ ((j : ℕ) - i) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  calc d i ≤ 4 ^ ((j : ℕ) - i) * d j := h1
    _ ≤ 4 ^ n * d j := by gcongr; exact hS.nonneg j

theorem lowerBlock_eq_zero_of_gap : ∀ (n : ℕ) (K c : ℝ), ∃ R : ℝ, 1 ≤ R ∧ ∀ (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), GlobalTheory.RedTh.IsSiegel d u → (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (∀ i j, j < i → v i j = 0) → (∀ i j, |v i j| ≤ c) → (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K) → ∀ k k' : Fin n, (k' : ℕ) = k + 1 → R * d k < d k' → ∀ p q, q ≤ k → k' ≤ p → (u * A.map (Int.cast : ℤ → ℝ) * v) p q = 0 := by
  intro n K c
  set C : ℝ := (n : ℝ) ^ 2 * (|c| + 1) with hC
  set X : ℝ := (|K| + 1) * C ^ 2 with hX
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by positivity
  have h16 : (0:ℝ) ≤ 16 ^ n * X := by positivity
  refine ⟨16 ^ n * X + 1, by linarith, ?_⟩
  intro A d u v hS hd hvu huv hvl hvc hsum k k' hkk' hR p q hqk hkp
  set B : Matrix (Fin n) (Fin n) ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  set Wm := u * B * v with hW

  have hratio : ∀ s t : Fin n, t ≤ k → k' ≤ s → X * d t < d s := by
    intro s t hts hks
    have h1 := chain_le hS t k hts
    have h2 := chain_le hS k' s hks
    have h4 : (0:ℝ) < 4 ^ n := by positivity
    have hdk := hd k
    have e16 : (16:ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
    have : 4 ^ n * (X * d t) < 4 ^ n * d s := by
      calc 4 ^ n * (X * d t) ≤ 4 ^ n * (X * (4 ^ n * d k)) := by gcongr
        _ = 16 ^ n * X * d k := by rw [e16]; ring
        _ < (16 ^ n * X + 1) * d k := by nlinarith
        _ < d k' := hR
        _ ≤ 4 ^ n * d s := h2
    exact lt_of_mul_lt_mul_left this h4.le

  have hterm : ∀ s t : Fin n, d s / d t * Wm s t ^ 2 ≤ K := by
    intro s t
    have hnn : ∀ a b : Fin n, 0 ≤ d a / d b * Wm a b ^ 2 := fun a b =>
      mul_nonneg (div_nonneg (hd a).le (hd b).le) (sq_nonneg _)
    calc d s / d t * Wm s t ^ 2 ≤ ∑ q, d s / d q * Wm s q ^ 2 :=
          Finset.single_le_sum (f := fun q => d s / d q * Wm s q ^ 2) (fun q _ => hnn s q) (Finset.mem_univ t)
      _ ≤ ∑ p, ∑ q, d p / d q * Wm p q ^ 2 :=
          Finset.single_le_sum (f := fun p => ∑ q, d p / d q * Wm p q ^ 2)
            (fun p _ => Finset.sum_nonneg (fun q _ => hnn p q)) (Finset.mem_univ s)
      _ ≤ K := hsum
  have hWsmall : ∀ s t : Fin n, t ≤ k → k' ≤ s → C * |Wm s t| < 1 := by
    intro s t hts hks
    have hr := hratio s t hts hks
    have hdt := hd t
    have hXr : X < d s / d t := by rw [lt_div_iff₀ hdt]; exact hr
    have h1 : X * Wm s t ^ 2 ≤ K := le_trans (mul_le_mul_of_nonneg_right hXr.le (sq_nonneg _)) (hterm s t)
    have h2 : C ^ 2 * Wm s t ^ 2 < 1 := by
      have hK : K ≤ |K| := le_abs_self K
      by_contra hcon
      push_neg at hcon
      have : (|K| + 1) * 1 ≤ (|K| + 1) * (C ^ 2 * Wm s t ^ 2) := by gcongr
      nlinarith
    have h3 : (C * |Wm s t|) ^ 2 < 1 := by rw [mul_pow, sq_abs]; exact h2
    have h4 : 0 ≤ C * |Wm s t| := by positivity
    nlinarith
  have hrec : B = v * Wm * u := by
    rw [hW]; simp only [← Matrix.mul_assoc]
    rw [hvu, Matrix.one_mul, Matrix.mul_assoc, hvu, Matrix.mul_one]
  have hAzero : ∀ i j : Fin n, k' ≤ i → j ≤ k → A i j = 0 := by
    intro i j hi hj
    have hent : (A i j : ℝ) = ∑ t, (∑ s, v i s * Wm s t) * u t j := by
      have : B i j = (v * Wm * u) i j := by rw [← hrec]
      simpa [hB, Matrix.mul_apply] using this
    have hn : (0:ℝ) < (n:ℝ) ^ 2 := by have := Fin.pos i; positivity
    have key : ∀ s t : Fin n, |v i s * Wm s t * u t j| < 1 / (n:ℝ) ^ 2 := by
      intro s t
      by_cases hs : s < i
      · rw [hvl i s hs]; simp; positivity
      by_cases ht : j < t
      · rw [hS.lower t j ht]; simp; positivity
      push_neg at hs ht
      have hsm := hWsmall s t (le_trans ht hj) (le_trans hi hs)
      have hu1 : |u t j| ≤ 1 := by
        rcases eq_or_lt_of_le ht with h | h
        · rw [h, hS.diag]; simp
        · have := hS.upper t j h; linarith
      have hv1 : |v i s| ≤ |c| + 1 := by
        have := hvc i s; have := le_abs_self c; linarith
      rw [abs_mul, abs_mul]
      calc |v i s| * |Wm s t| * |u t j| ≤ (|c| + 1) * |Wm s t| * 1 := by gcongr
        _ < 1 / (n:ℝ) ^ 2 := by
          rw [lt_div_iff₀ hn]
          have : (|c| + 1) * |Wm s t| * 1 * (n:ℝ) ^ 2 = C * |Wm s t| := by rw [hC]; ring
          linarith
    have hbound : |(A i j : ℝ)| < 1 := by
      rw [hent]
      calc |∑ t, (∑ s, v i s * Wm s t) * u t j| = |∑ t, ∑ s, v i s * Wm s t * u t j| := by
            simp [Finset.sum_mul]
        _ ≤ ∑ t, ∑ s, |v i s * Wm s t * u t j| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => Finset.abs_sum_le_sum_abs _ _)
        _ < ∑ t : Fin n, ∑ s : Fin n, 1 / (n:ℝ) ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun t _ =>
              Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun s _ => key s t
        _ = 1 := by
            have : (n:ℝ) ≠ 0 := by have := Fin.pos i; positivity
            simp; field_simp
    have : |A i j| < 1 := by exact_mod_cast hbound
    exact Int.abs_lt_one_iff.mp this
  rw [hW]
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : q < t
  · simp [hvl t q ht]
  push_neg at ht
  have hz : ∑ s, u p s * B s t = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s < p
    · simp [hS.lower p s hs]
    push_neg at hs
    simp [hB, hAzero s t (le_trans hkp hs) (le_trans ht hqk)]
  rw [hz, zero_mul]

end GlobalTheory.SiegelGap
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelDomain_lowerBlock_eq_zero_of_large_gap : ∀ (n : ℕ) (K c : ℝ), ∃ R : ℝ, 1 ≤ R ∧ ∀ (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (∀ i j, j < i → v i j = 0) → (∀ i j, |v i j| ≤ c) → (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K) → ∀ k k' : Fin n, (k' : ℕ) = k + 1 → R * d k < d k' → ∀ p q, q ≤ k → k' ≤ p → (u * A.map (Int.cast : ℤ → ℝ) * v) p q = 0 := by
  atlas_forward_decl GlobalTheory.SiegelGap.lowerBlock_eq_zero_of_gap
end

section
section
noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem term_le_double_sum {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ p q, 0 ≤ f p q) (p q : Fin n) :
    f p q ≤ ∑ p, ∑ q, f p q := by
  calc f p q ≤ ∑ q, f p q := Finset.single_le_sum (fun q _ => hf p q) (Finset.mem_univ q)
    _ ≤ ∑ p, ∑ q, f p q := Finset.single_le_sum (f := fun p => ∑ q, f p q)
        (fun p _ => Finset.sum_nonneg fun q _ => hf p q) (Finset.mem_univ p)

theorem step_chain {n : ℕ} {d : Fin n → ℝ} (hs : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q)
    (q : Fin n) : ∀ m (hm : (q : ℕ) + m < n), d q ≤ 4 ^ m * d ⟨q + m, hm⟩ := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hs ⟨q + m, by omega⟩ ⟨q + (m + 1), hm⟩ (by simp; omega)
    calc d q ≤ 4 ^ m * d ⟨q + m, by omega⟩ := h1
      _ ≤ 4 ^ m * (4 * d ⟨q + (m + 1), hm⟩) := by gcongr
      _ = 4 ^ (m + 1) * d ⟨q + (m + 1), hm⟩ := by ring

theorem gap_chain {n : ℕ} {d : Fin n → ℝ} {R : ℝ} (hR : 0 ≤ R) (p : Fin n) :
    ∀ m (hm : (p : ℕ) + m < n),
      (∀ k k' : Fin n, (k' : ℕ) = k + 1 → p ≤ k → (k' : ℕ) ≤ p + m → d k' ≤ R * d k) →
      d ⟨p + m, hm⟩ ≤ R ^ m * d p := by
  intro m
  induction m with
  | zero => intro hm _; simp
  | succ m ih =>
    intro hm h
    have h1 := ih (by omega) (fun k k' hk hpk hk' => h k k' hk hpk (by omega))
    have h2 := h ⟨p + m, by omega⟩ ⟨p + (m + 1), hm⟩ (by simp; omega)
      (by simp [Fin.le_def]) (by simp)
    calc d ⟨p + (m + 1), hm⟩ ≤ R * d ⟨p + m, by omega⟩ := h2
      _ ≤ R * (R ^ m * d p) := by gcongr
      _ = R ^ (m + 1) * d p := by ring

theorem balanced_entries_bounded : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) →
    (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) →
    (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  intro n K
  obtain ⟨c, hc⟩ := GlobalTheory.T.siegelUnipotent_inverse_entries_bounded n
  obtain ⟨R, hR1, hR⟩ := GlobalTheory.T.siegelDomain_lowerBlock_eq_zero_of_large_gap n K c
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hRn : (1 : ℝ) ≤ R ^ n := one_le_pow₀ hR1
  have hB : 0 ≤ 4 ^ n * R ^ n * max K 0 := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0
  refine ⟨(n : ℝ) ^ 2 * |c| * (1 + 4 ^ n * R ^ n * max K 0), ?_⟩
  intro A A' d u hS hd hbal htr i j
  obtain ⟨v, hvu, huv, hvl, hvc⟩ := hc u hS.diag hS.lower hS.upper
  obtain ⟨hsym, hsum, hsum'⟩ := GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace n A A' d u v hd hvu huv hbal
  have hK' : ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum']; exact htr
  have hK : ∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum]; exact htr
  set Ar := A.map (Int.cast : ℤ → ℝ) with hAr
  set W := u * Ar * v with hWdef
  set B := 4 ^ n * R ^ n * max K 0 with hBdef
  have hterm : ∀ p q, d p / d q * W p q ^ 2 ≤ max K 0 := fun p q =>
    (term_le_double_sum (fun p q => d p / d q * W p q ^ 2)
      (fun p q => mul_nonneg (div_nonneg (hd p).le (hd q).le) (sq_nonneg _)) p q).trans
      (hK.trans (le_max_left _ _))
  have hsq : ∀ p q, W p q ^ 2 ≤ d q / d p * max K 0 := by
    intro p q
    have hp := (hd p).ne'
    have hq := (hd q).ne'
    have e : W p q ^ 2 = d q / d p * (d p / d q * W p q ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hterm p q) (div_nonneg (hd q).le (hd p).le)
  have hW : ∀ p q, W p q ^ 2 ≤ B := by
    intro p q
    rcases le_or_gt q p with hqp | hpq
    · have hqp' : (q : ℕ) ≤ p := hqp
      have hm : (q : ℕ) + ((p : ℕ) - q) < n := by omega
      have h1 := step_chain hS.step q ((p : ℕ) - q) hm
      have hpe : (⟨(q : ℕ) + ((p : ℕ) - q), hm⟩ : Fin n) = p := by ext; simp; omega
      rw [hpe] at h1
      have h2 : (4 : ℝ) ^ ((p : ℕ) - q) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : d q ≤ 4 ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
      have h5 : d q / d p ≤ 4 ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
      calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
        _ ≤ 4 ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
        _ ≤ 4 ^ n * max K 0 * R ^ n := le_mul_of_one_le_right (by positivity) hRn
        _ = B := by rw [hBdef]; ring
    · have hpq' : (p : ℕ) < q := hpq
      by_cases hgap : ∃ k k' : Fin n, (k' : ℕ) = k + 1 ∧ p ≤ k ∧ k' ≤ q ∧ R * d k < d k'
      · obtain ⟨k, k', hk, hpk, hkq, hlt⟩ := hgap
        have h0 : (u * A'.map (Int.cast : ℤ → ℝ) * v) q p = 0 :=
          hR A' d u v hS hd hvu huv hvl hvc hK' k k' hk hlt q p hpk hkq
        have h1 := hsym p q
        rw [h0, mul_zero] at h1
        have hz : W p q = 0 := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h (hd p).ne'
          · exact h
        rw [hz]
        simpa using hB
      · push_neg at hgap
        have hm : (p : ℕ) + ((q : ℕ) - p) < n := by omega
        have h1 := gap_chain (d := d) (by linarith) p ((q : ℕ) - p) hm
          (fun k k' hk hpk hk' => hgap k k' hk hpk (by rw [Fin.le_def]; omega))
        have hqe : (⟨(p : ℕ) + ((q : ℕ) - p), hm⟩ : Fin n) = q := by ext; simp; omega
        rw [hqe] at h1
        have h2 : R ^ ((q : ℕ) - p) ≤ R ^ n := pow_le_pow_right₀ hR1 (by omega)
        have h3 : d q ≤ R ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
        have h5 : d q / d p ≤ R ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
        calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
          _ ≤ R ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
          _ ≤ 4 ^ n * (R ^ n * max K 0) := le_mul_of_one_le_left (by positivity) h4
          _ = B := by rw [hBdef]; ring
  have hA : Ar = v * W * u := by
    calc Ar = (v * u) * Ar * (v * u) := by rw [hvu, Matrix.one_mul, Matrix.mul_one]
      _ = v * W * u := by rw [hWdef]; simp only [Matrix.mul_assoc]
  have hu1 : ∀ l j, |u l j| ≤ 1 := by
    intro l j
    rcases lt_trichotomy l j with h | h | h
    · exact (hS.upper l j h).trans (by norm_num)
    · subst h; rw [hS.diag]; simp
    · rw [hS.lower l j h]; simp
  have hWb : ∀ k l, |W k l| ≤ 1 + B := fun k l => by
    nlinarith [hW k l, abs_nonneg (W k l), sq_abs (W k l)]
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hentry : |Ar i j| ≤ (n : ℝ) ^ 2 * |c| * (1 + B) := by
    rw [hA, Matrix.mul_apply]
    calc |∑ l, (v * W) i l * u l j| ≤ ∑ l, |(v * W) i l * u l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin n, (n : ℝ) * (|c| * (1 + B)) := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_mul, Matrix.mul_apply]
        have hin : |∑ k, v i k * W k l| ≤ (n : ℝ) * (|c| * (1 + B)) := by
          calc |∑ k, v i k * W k l| ≤ ∑ k, |v i k * W k l| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k : Fin n, |c| * (1 + B) := by
              apply Finset.sum_le_sum; intro k _
              rw [abs_mul]
              exact mul_le_mul ((hvc i k).trans (le_abs_self c)) (hWb k l) (abs_nonneg _) hc0
            _ = (n : ℝ) * (|c| * (1 + B)) := by simp
        calc |∑ k, v i k * W k l| * |u l j| ≤ (n : ℝ) * (|c| * (1 + B)) * 1 :=
              mul_le_mul hin (hu1 l j) (abs_nonneg _) (by positivity)
          _ = (n : ℝ) * (|c| * (1 + B)) := by ring
      _ = (n : ℝ) ^ 2 * |c| * (1 + B) := by simp; ring
  have hcast : ((|A i j| : ℤ) : ℝ) = |Ar i j| := by simp [hAr, Int.cast_abs]
  rw [hcast]
  exact hentry

end GlobalTheory.RedTh
end
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balanced_entries_bounded_siegelReduced : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  atlas_forward_decl GlobalTheory.RedTh.balanced_entries_bounded
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem trace_le_of_aeval_monic_eq_zero :
    ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ,
      Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  intro p hp n
  set pC : Polynomial ℂ := p.map (Int.castRingHom ℂ) with hpC
  have hpC0 : pC ≠ 0 := (hp.map (Int.castRingHom ℂ)).ne_zero
  set B : ℝ := ∑ x ∈ pC.roots.toFinset, ‖x‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun x _ => norm_nonneg x
  refine ⟨n * B, fun M hM => ?_⟩
  set A : Matrix (Fin n) (Fin n) ℂ := M.map (Int.castRingHom ℂ) with hA
  have hAp : Polynomial.aeval A pC = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Int.castRingHom ℂ).mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hM, map_zero] at e
    rw [hpC, show Int.castRingHom ℂ = algebraMap ℤ ℂ from rfl, Polynomial.aeval_map_algebraMap]
    exact e
  have htr : ((M.trace : ℤ) : ℂ) = A.trace := by
    simp [hA, Matrix.trace, Matrix.map_apply]
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ B := by
    intro μ hμ
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exfalso
      have hc := Polynomial.card_roots' A.charpoly
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_eq_zero] at hc
      have := Multiset.card_pos_iff_exists_mem.2 ⟨μ, hμ⟩
      omega
    have hsp : μ ∈ spectrum ℂ A :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hμ)
    have h1 := spectrum.subset_polynomial_aeval A pC ⟨μ, hsp, rfl⟩
    rw [hAp, spectrum.zero_eq, Set.mem_singleton_iff] at h1
    have hmem : μ ∈ pC.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpC0]; exact h1
    exact Finset.single_le_sum (f := fun x => ‖x‖) (fun x _ => norm_nonneg x) hmem
  have hsum : ‖A.trace‖ ≤ n * B := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine (norm_multiset_sum_le _).trans ?_
    refine (Multiset.sum_le_card_nsmul _ B (fun x hx => by obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hx; exact hroot μ hμ)).trans ?_
    rw [Multiset.card_map, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hB0
    have := Polynomial.card_roots' A.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact_mod_cast this
  calc ((M.trace : ℤ) : ℝ) = (((M.trace : ℤ) : ℂ)).re := by simp
    _ ≤ ‖((M.trace : ℤ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ n * B := by rw [htr]; exact hsum

end GlobalTheory.RedTh
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero : ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ, Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  atlas_forward_decl GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero
end

section
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem finite_balanced_actions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ),
    {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  intro E _ _ _ H n
  classical
  set S := {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)} with hSdef

  have hK : ∀ c : 𝓞 E, ∃ K : ℝ, ∀ ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ,
      (((ρ (H.bar c) * ρ c).trace : ℤ) : ℝ) ≤ K := by
    intro c
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) (H.bar c * c)
    obtain ⟨K, hK⟩ := GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero p hpm n
    refine ⟨K, fun ρ => ?_⟩
    apply hK
    have h0 : Polynomial.aeval (ρ.toIntAlgHom (H.bar c * c)) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hp, map_zero]
    simpa using h0
  choose K hK using hK

  have hC : ∀ c : 𝓞 E, ∃ N : ℤ, ∀ ρ ∈ S, ∀ i j, ρ c i j ∈ Set.Icc (-N) N := by
    intro c
    obtain ⟨C, hC⟩ := GlobalTheory.T.balanced_entries_bounded_siegelReduced n (K c)
    refine ⟨⌈C⌉, fun ρ hρ i j => ?_⟩
    obtain ⟨d, u, hs, hpos, hrel⟩ := hρ
    have h1 := hC (ρ c) (ρ (H.bar c)) d u hs hpos (hrel c) (hK c ρ) i j
    have h2 : ((|ρ c i j| : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := h1.trans (Int.le_ceil C)
    have h3 : |ρ c i j| ≤ ⌈C⌉ := by exact_mod_cast h2
    exact abs_le.mp h3
  choose N hN using hC
  let b := RingOfIntegers.basis E
  let F : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    fun ρ l => ρ (b l)
  let T : Set (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    Set.pi Set.univ fun l => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-N (b l)) (N (b l))
  have hT : T.Finite :=
    Set.Finite.pi fun l => Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine Set.Finite.of_injOn (f := F) (t := T) ?_ ?_ hT
  · intro ρ hρ l _ i _ j _
    exact hN (b l) ρ hρ i j
  · intro ρ₁ _ ρ₂ _ h
    have hl : ∀ l, ρ₁ (b l) = ρ₂ (b l) := fun l => congrFun h l
    have hlin : ρ₁.toAddMonoidHom.toIntLinearMap = ρ₂.toAddMonoidHom.toIntLinearMap :=
      b.ext fun l => by simpa using hl l
    ext1 x
    simpa using LinearMap.congr_fun hlin x

end GlobalTheory.RedTh
end

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_balanced_cmIntegers_actions_siegelReduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  atlas_forward_decl GlobalTheory.RedTh.finite_balanced_actions
end

section
noncomputable section

open Matrix NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

section Cover

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem hasRedCover_of_fintype (bar : O → O) {ι : Type} [Fintype ι] (f : ι → LinearMap.BilinForm ℤ X)
    (h1 : ∀ i y z, f i y z = f i z y) (h2 : ∀ i y, 0 ≤ f i y y)
    (h : ∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (c : ι → ℝ), (∀ i, 0 ≤ c i) ∧
      pullR e.toLinearMap B = ∑ i, c i • toReal (f i)) : HasRedCover bar X := by
  let q := Fintype.equivFin ι
  refine ⟨1, fun _ => Fintype.card ι, fun _ i => f (q.symm i), fun _ i => h1 _, fun _ i => h2 _, fun B hB => ?_⟩
  obtain ⟨e, c, hc, he⟩ := h B hB
  refine ⟨e, 0, fun i => c (q.symm i), fun i => hc _, ?_⟩
  rw [he]
  exact (q.symm.sum_comp fun i => c i • toReal (f i)).symm

def sqForm {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) : LinearMap.BilinForm ℤ X :=
  let φ : X →ₗ[ℤ] ℤ := ∑ i, l i • b.coord i
  (LinearMap.mul ℤ ℤ).compl₁₂ φ φ

theorem sqForm_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (y z : X) :
    sqForm b l y z = (∑ i, l i * b.repr y i) * ∑ i, l i * b.repr z i := by
  simp [sqForm, LinearMap.sum_apply]
  rw [Finset.sum_mul_sum, Finset.sum_comm]

theorem sqForm_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (i j : Fin n) :
    sqForm b l (b i) (b j) = l i * l j := by
  simp [sqForm_apply, Finsupp.single_apply]

theorem exists_equiv_of_actMat_eq {n : ℕ} (b b' : Module.Basis (Fin n) ℤ X)
    (h : (actMat b : O →+* _) = actMat b') : ∃ e : X ≃ₗ[O] X, ∀ i, e (b i) = b' i := by
  let g : X ≃ₗ[ℤ] X := b.equiv b' (Equiv.refl _)
  have hg : ∀ i, g (b i) = b' i := fun i => by simp [g]
  have key : ∀ (c : O) (x : X), g (c • x) = c • g x := by
    intro c x
    have h1 : (g.toLinearMap ∘ₗ (Module.toModuleEnd ℤ X c)) = (Module.toModuleEnd ℤ X c) ∘ₗ g.toLinearMap := by
      refine b.ext fun j => ?_
      change g (c • b j) = c • g (b j)
      rw [hg]
      calc g (c • b j) = g (∑ i, b.repr (c • b j) i • b i) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (c • b j) i • b' i := by simp only [map_sum, map_smul, hg]
        _ = ∑ i, b'.repr (c • b' j) i • b' i := Finset.sum_congr rfl fun i _ => by
            have := congrFun (congrFun (congrArg (fun ρ : O →+* Matrix (Fin n) (Fin n) ℤ => ρ c) h) i) j
            simp only [actMat_apply] at this
            rw [this]
        _ = c • b' j := b'.sum_repr _
    exact LinearMap.congr_fun h1 x
  exact ⟨(g.toAddEquiv).toLinearEquiv key, hg⟩

theorem actMat_balanced {bar : O → O} {n : ℕ} (b : Module.Basis (Fin n) ℤ X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ realForms bar X) {G : Matrix (Fin n) (Fin n) ℝ} (hG : ∀ i j, B (b i) (b j) = G i j) (c : O) :
    ((actMat b c).map (Int.cast : ℤ → ℝ))ᵀ * G = G * (actMat b (bar c)).map (Int.cast : ℤ → ℝ) := by
  ext i j
  have e1 : B (c • b i) (b j) = ∑ k, (b.repr (c • b i) k : ℝ) * G k j :=
    calc B (c • b i) (b j) = B (∑ k, b.repr (c • b i) k • b k) (b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hG, zsmul_eq_mul]
  have e2 : B (b i) (bar c • b j) = ∑ k, G i k * (b.repr (bar c • b j) k : ℝ) :=
    calc B (b i) (bar c • b j) = B (b i) (∑ k, b.repr (bar c • b j) k • b k) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, hG, zsmul_eq_mul, mul_comm]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, actMat_apply]
  rw [← e1, ← e2]
  exact hB.2 c _ _

end Cover

theorem hasRedCover (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] : HasRedCover H.bar X := by
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨i, hi⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) X)
    exact Module.Projective.of_split (i.restrictScalars ℤ) ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hi x)
  haveI : Module.Free ℤ X := inferInstance
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀, hB₀'⟩ := GlobalTheory.T.exists_posDef_balanced_realForm_cmField E H X
  have hF := GlobalTheory.T.finite_balanced_cmIntegers_actions_siegelReduced E H n
  obtain ⟨S, hS⟩ := GlobalTheory.T.siegelGram_mem_cone_integer_squares n
  haveI : Nonempty (Module.Basis (Fin n) ℤ X) := ⟨Module.finBasisOfFinrankEq ℤ X hn⟩
  let ref : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → Module.Basis (Fin n) ℤ X := fun ρ => Classical.epsilon fun b => actMat b = ρ
  let ι := ↥hF.toFinset × ↥S
  refine hasRedCover_of_fintype (ι := ι) _ (fun x => sqForm (ref x.1.1) x.2.1) (fun x y z => ?_) (fun x y => ?_) fun B hB => ?_
  · simp only [sqForm_apply, mul_comm]
  · simp only [sqForm_apply]; exact mul_self_nonneg _
  obtain ⟨b, d, d', u, B', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms E H X B₀ hB₀ hB₀' n hn B hB
  have hρ : (actMat b : 𝓞 E →+* _) ∈ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨d', u, h2, h3, fun c => actMat_balanced b h4 h6 c⟩
  set ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ := actMat b with hρdef
  have href : actMat (ref ρ) = ρ := Classical.epsilon_spec (p := fun b => actMat b = ρ) ⟨b, rfl⟩
  obtain ⟨e, he⟩ := exists_equiv_of_actMat_eq (O := 𝓞 E) (ref ρ) b href
  obtain ⟨c, hc, hG⟩ := hS d u h1
  refine ⟨e, fun x => if x.1.1 = ρ then c x.2.1 else 0, fun x => ?_, ?_⟩
  · dsimp only; split_ifs
    · exact hc _
    · exact le_rfl
  refine (ref ρ).ext fun i => (ref ρ).ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [h5, hG]
    simp [Matrix.sum_apply, vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨ρ, hρ⟩ : ↥hF.toFinset)]
  · simp only [if_true, sqForm_basis]
    rw [← Finset.sum_coe_sort S]
    push_cast
    rfl
  · intro y _ hy
    have : y.1 ≠ ρ := fun h => hy (Subtype.ext h)
    simp [this]
  · simp

end GlobalTheory.RedTh
end
end
