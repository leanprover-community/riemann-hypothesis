import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.GsFrCut

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section defs

variable (k r : ℕ)

def Xsp : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ (Set.range fun a : Fin r => bvec (eI k r a))

def Wsp (z : Fin (2 * r + k + 1) → ℂ) : Set (Fin (2 * r + k + 1) → ℂ) :=
  {v | inWb k r v ∧ herm (Hpk k r) v z = 0}

def wbPart (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0

def prW (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  wbPart k r v + (herm (Hpk k r) (wbPart k r v) z / (Tz k r z : ℂ)) • z

def xcof (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ b, (Zhat k r z z' g).adjugate b (Fin.last r) • (g *ᵥ fvec k r z' b)

def xcofL (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a

def omW (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ := prW k r z (xcof k r z z' g)

def omW' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)

end defs

structure GfBaseD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) where
  nu : Fin (2 * r + k + 1) → ℂ
  nu' : Fin (2 * r + k + 1) → ℂ
  U0 : Set (Fin (2 * r + k + 1) → ℂ)
  nu_mem : nu ∈ Wsp k r z
  nu_unit : herm (Hpk k r) nu nu = 1
  nu'_mem : nu' ∈ Wsp k r z'
  nu'_unit : herm (Hpk k r) nu' nu' = 1
  isotropic_subspace_eq : ∀ u, u ∈ U0 ↔ u ∈ Wsp k r z ∧ herm (Hpk k r) u nu = 0
  isotropic_subspace_eq_primed : ∀ u, u ∈ U0 ↔ u ∈ Wsp k r z' ∧ herm (Hpk k r) u nu' = 0

def gfSig {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (D0 : GfBaseD k r z z') : Set (B.Mat k r) :=
  {y | y ∈ B.GV k r ∧ 0 < Gf k r z z' y ∧
    (∃ t : ℝ, 0 < t ∧ omW k r z z' y = (t : ℂ) • D0.nu) ∧ (∃ t : ℝ, 0 < t ∧ omW' k r z z' y = (t : ℂ) • D0.nu') ∧
    ∀ u ∈ D0.U0, ∃ v ∈ Xsp k r, ∃ v' ∈ Xsp k r, y *ᵥ (u + v') = u + v}

def GfBase : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    Nonempty (GfBaseD k r z z')

def GfSat : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, n * y * n' ∈ gfSig D0

def GfStab : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z',
      α * y * β ∈ gfSig D0 → Rel z z' y (α * y * β)

def GfLocal : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ →
      ∃ (O : Set (B.Mat k r)) (Fl : B.Mat k r → B.Mat k r × B.Mat k r),
        IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl O ∧
        ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          (Fl g).1 ∈ UWset k r z ∧ (Fl g).2 ∈ UWset k r z' ∧ (Fl g).1 * g * (Fl g).2 ∈ gfSig D0




end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section herm

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

lemma hm_add_l (x y w : Fin m → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, Matrix.mulVec_add]

lemma hm_sub_l (x y w : Fin m → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  simp [herm, Matrix.mulVec_sub]

lemma hm_smul_l (c : ℂ) (x w : Fin m → ℂ) : herm H (c • x) w = c * herm H x w := by
  simp [herm, Matrix.mulVec_smul]

lemma hm_add_r (x w w' : Fin m → ℂ) : herm H x (w + w') = herm H x w + herm H x w' := by
  simp [herm]

lemma hm_sub_r (x w w' : Fin m → ℂ) : herm H x (w - w') = herm H x w - herm H x w' := by
  simp [herm]

lemma hm_smul_r (c : ℂ) (x w : Fin m → ℂ) : herm H x (c • w) = star c * herm H x w := by
  simp [herm]

lemma hm_symm (hH : Hᴴ = H) (x y : Fin m → ℂ) : herm H y x = star (herm H x y) := by
  have hij : ∀ i j, H j i = star (H i j) := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  simp only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hij]
  ring

lemma hm_self_re (hH : Hᴴ = H) (x : Fin m → ℂ) : herm H x x = ((herm H x x).re : ℂ) := by
  have h := hm_symm H hH x x
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

end herm

lemma Hb_ct (k : ℕ) : (Hb k)ᴴ = Hb k := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Hb, Matrix.conjTranspose_apply]
    try (split_ifs <;> simp)
  · simp [Hb, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]

lemma re_Hb (k : ℕ) (u : Fin (k + 1) → ℂ) :
    (herm (Hb k) u u).re = (∑ i : Fin k, Complex.normSq (u i.castSucc)) - Complex.normSq (u (Fin.last k)) := by
  have hne : ∀ i : Fin k, (Fin.castSucc i = Fin.last k) = False :=
    fun i => eq_false (ne_of_lt (Fin.castSucc_lt_last i))
  simp [herm, Hb, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Complex.re_sum,
    Complex.normSq_apply, hne] <;> ring

lemma pos_b {k : ℕ} {zb u : Fin (k + 1) → ℂ} (hz : (herm (Hb k) zb zb).re < 0) (hu : herm (Hb k) u zb = 0)
    (hu0 : u ≠ 0) : 0 < (herm (Hb k) u u).re := by
  by_contra hle
  push Not at hle
  by_cases hl : u (Fin.last k) = 0
  · apply hu0
    rw [re_Hb, hl] at hle
    simp only [map_zero, sub_zero] at hle
    have hs : ∀ i ∈ (Finset.univ : Finset (Fin k)), Complex.normSq (u i.castSucc) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1
        (le_antisymm hle (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _))
    funext i
    refine Fin.lastCases hl (fun j => ?_) i
    exact Complex.normSq_eq_zero.1 (hs j (Finset.mem_univ _))
  · set a := zb (Fin.last k)
    set b := -(u (Fin.last k))
    set v := a • u + b • zb with hv
    have hzu : herm (Hb k) zb u = 0 := by rw [hm_symm _ (Hb_ct k), hu, star_zero]
    have hvv : herm (Hb k) v v = a * star a * herm (Hb k) u u + b * star b * herm (Hb k) zb zb := by
      simp only [hv, hm_add_l, hm_add_r, hm_smul_l, hm_smul_r, hu, hzu]
      ring
    have hvl : v (Fin.last k) = 0 := by
      simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b]; ring
    have h1 : 0 ≤ (herm (Hb k) v v).re := by
      rw [re_Hb, hvl]; simp only [map_zero, sub_zero]
      exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hb : 0 < Complex.normSq b := Complex.normSq_pos.2 (neg_ne_zero.2 hl)
    have h2 : (herm (Hb k) v v).re = Complex.normSq a * (herm (Hb k) u u).re +
        Complex.normSq b * (herm (Hb k) zb zb).re := by
      rw [hvv, Complex.add_re]
      simp only [Complex.star_def]
      rw [Complex.mul_conj, Complex.mul_conj, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : Complex.normSq a * (herm (Hb k) u u).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle
    nlinarith

section vec

variable {k r : ℕ}

lemma posV {z u : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hu : inWb k r u)
    (huz : herm (Hpk k r) u z = 0) (hu0 : u ≠ 0) : 0 < (herm (Hpk k r) u u).re := by
  have eu := Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hu
  have ez := Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz.1
  rw [← eu, ← ez, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV] at huz
  rw [← eu, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV]
  refine pos_b ?_ huz ?_
  · have h2 := hz.2
    unfold Tz at h2
    rw [← ez, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV] at h2
    linarith
  · intro h
    apply hu0
    rw [← eu, h]
    funext i
    simp [Formalism.FourierDecayAlt.P.TwoByOneBlock.jV]

def pOut (k r : ℕ) (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  v - (herm (Hpk k r) v z / herm (Hpk k r) z z) • z

def nz (k r : ℕ) (p : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  (((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ) • p

lemma hzz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  have h2 : 0 < Tz k r z := by
    unfold C2.StdZ at hz
    exact hz.2
  unfold Tz at h2
  rw [h] at h2
  simp at h2

lemma z_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : z ≠ 0 := by
  intro h
  apply hzz_ne hz
  rw [h]
  simp [herm]




lemma nz_inWb {p : Fin (2 * r + k + 1) → ℂ} (hp : inWb k r p) : inWb k r (nz k r p) := by
  unfold nz
  intro i hi
  simp [hp i hi]

lemma nz_herm_l (p w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (nz k r p) w = (((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ) * herm (Hpk k r) p w := by
  unfold nz
  rw [hm_smul_l]

lemma nz_orth {p : Fin (2 * r + k + 1) → ℂ} (hp : 0 < (herm (Hpk k r) p p).re) (u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u (nz k r p) = 0 ↔ herm (Hpk k r) u p = 0 := by
  unfold nz
  rw [hm_smul_r]
  have hc : star ((((Real.sqrt (herm (Hpk k r) p p).re)⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    rw [star_ne_zero]
    exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc, fun h => by rw [h, mul_zero]⟩

lemma nz_unit {p : Fin (2 * r + k + 1) → ℂ} (hp : 0 < (herm (Hpk k r) p p).re) :
    herm (Hpk k r) (nz k r p) (nz k r p) = 1 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  unfold nz
  rw [hm_smul_l, hm_smul_r, hm_self_re _ hH p]
  set t := (herm (Hpk k r) p p).re with ht
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt hp.le
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  norm_cast
  field_simp
  linarith

end vec


end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def SatOm : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ y ∈ B.GV k r, 0 < Gf k r z z' y → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      omW k r z z' (n * y * n') = omW k r z z' y

def SatOm' : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ y ∈ B.GV k r, 0 < Gf k r z z' y → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      omW' k r z z' (n * y * n') = omW' k r z z' y

section lemmas

variable {k r : ℕ}

lemma mem_Xsp_iff (v : Fin (2 * r + k + 1) → ℂ) : v ∈ Xsp k r ↔ ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro i hi
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro h
      have ha := a.isLt
      rw [h] at hi
      simp only [eI] at hi
      omega
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul c x _ hx => intro i hi; simp [hx i hi]
  · intro hv
    have hsum : v = ∑ a : Fin r, v (eI k r a) • bvec (eI k r a) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : i.val < r
      · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
        · have he : i = eI k r ⟨i.val, hi⟩ := by ext; rfl
          rw [if_pos he, ← he]
        · intro b _ hb
          rw [if_neg]
          intro h
          apply hb
          ext
          show b.val = i.val
          have h2 := congrArg Fin.val h
          simp only [eI] at h2
          omega
        · simp
      · rw [hv i (by omega)]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [if_neg]
        intro h
        have hb := b.isLt
        rw [h] at hi
        simp only [eI] at hi
        omega
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)


lemma N_wb {n : B.Mat k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ Xsp k r := by
  rw [mem_Xsp_iff]
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [sub_eq_zero, Finset.sum_eq_single i]
  · by_cases hmid : i.val ≤ r + k
    · rw [hn.2.2 i i hi hmid hi, if_pos rfl, one_mul]
    · rw [hu i (Or.inr (by omega)), mul_zero]
  · intro j _ hji
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [hn.2.2 i j hj.1 hj.2 hi, if_neg (Ne.symm hji), zero_mul]
    · rw [hu j (by omega), mul_zero]
  · simp

end lemmas


end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section om

variable {k r : ℕ}

lemma mv_sum {ι : Type*} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Finset ι)
    (v : ι → Fin (2 * r + k + 1) → ℂ) : M *ᵥ (∑ i ∈ s, v i) = ∑ i ∈ s, M *ᵥ v i := by
  first
  | exact Matrix.mulVec_sum M s v
  | simpa using map_sum (Matrix.mulVecLin M) v s
  | (induction s using Finset.cons_induction with
     | empty => simp
     | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.mulVec_add, ih])

lemma hm_sum_l {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * herm (Hpk k r) (v i) w := by
  unfold herm
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    rw [Matrix.mulVec_add, ← ih]
    simp [Matrix.mulVec_smul]

lemma hm_sum_r {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w (∑ i ∈ s, c i • v i) = ∑ i ∈ s, star (c i) * herm (Hpk k r) w (v i) := by
  unfold herm
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.sum_cons, star_add]
    rw [← ih]
    simp [star_smul]

lemma herm_bvec_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  have ha := a.isLt
  have key : ∀ j, Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
    intro j
    by_cases hj : j = esI k r a
    · subst hj
      rw [if_pos rfl]
      simp only [Hpk, eI, esI, Fin.val_mk]
      have h3 : ¬ r ≤ (a : ℕ) := by omega
      simp only [h3, false_and, if_false]
      split_ifs <;> first | rfl | (exfalso; omega) | omega
    · rw [if_neg hj]
      have hj' : (j : ℕ) ≠ (esI k r a : ℕ) := fun h => hj (Fin.ext h)
      simp only [Hpk, eI, esI, Fin.val_mk] at hj' ⊢
      have h3 : ¬ r ≤ (a : ℕ) := by omega
      simp only [h3, false_and, if_false]
      split_ifs <;> first | rfl | (exfalso; omega) | omega
  unfold herm bvec
  have hs : star (Pi.single (eI k r a) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single (eI k r a) 1 := by
    ext i
    by_cases h : i = eI k r a <;> simp [Pi.single_apply, h]
  rw [hs]
  simp [key, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma fvec_lt (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
  unfold fvec
  first
  | exact dif_pos a.isLt
  | simp
  | rfl

lemma wb_N {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : PI.UnitaryGroupMassFormula.GsFr.wbPart k r (n *ᵥ v) = PI.UnitaryGroupMassFormula.GsFr.wbPart k r v := by
  simp only [Formalism.QuantumDeterminants.Nset, Set.mem_setOf_eq] at hn
  obtain ⟨-, h1, h2⟩ := hn
  funext i
  unfold wbPart
  split_ifs with hi
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · rw [h2 i i hi.1 hi.2 hi.1, if_pos rfl, one_mul]
    · intro j _ hji
      by_cases hj1 : j.val < r
      · have hle : (⟨j.val, hj1⟩ : Fin r).val ≤ i.val := by
          show j.val ≤ i.val
          omega
        have hc := h1 ⟨j.val, hj1⟩ i hle
        have he : eI k r ⟨j.val, hj1⟩ = j := Fin.ext rfl
        rw [he] at hc
        rw [hc, if_neg (fun h => hji h.symm), zero_mul]
      · by_cases hj2 : j.val ≤ r + k
        · rw [h2 i j (by omega) hj2 hi.1, if_neg (fun h => hji h.symm), zero_mul]
        · have hjl := j.isLt
          have hes : j = esI k r ⟨2 * r + k - j.val, by omega⟩ :=
            Fin.ext (by simp only [esI, Fin.val_mk]; omega)
          rw [hes, hv, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rfl

lemma prW_N {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : prW k r z (n *ᵥ v) = prW k r z v := by
  unfold prW
  rw [wb_N hn hv]

lemma adj_col (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (a : Fin (r + 1)) (ha : a ≠ Fin.last r) :
    ∑ b, Z.adjugate b (Fin.last r) * Z a b = 0 := by
  have h := congrFun (congrFun (Matrix.mul_adjugate Z) a) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne ha, smul_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma adj_row (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) (hb : b ≠ Fin.last r) :
    ∑ a, Z.adjugate (Fin.last r) a * Z a b = 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul Z) (Fin.last r)) b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hb), smul_zero] at h
  exact h

lemma xcof_esI (z z' : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r) (a : Fin r) :
    xcof k r z z' y (esI k r a) = 0 := by
  unfold xcof
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hrow : ∀ b, (y *ᵥ fvec k r z' b) (esI k r a) = Zhat k r z z' y ⟨a.val, by omega⟩ b := by
    intro b
    rw [← herm_bvec_eI (y *ᵥ fvec k r z' b) a, ← fvec_lt z a]
    rfl
  simp only [hrow]
  exact adj_col _ _ (by rw [Ne, Fin.ext_iff, Fin.val_last]; exact Nat.ne_of_lt a.isLt)

lemma unitri_det {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ C2.UTset m) : U.det = 1 := by
  have hU' : (∀ i j : Fin m, j < i → U i j = 0) ∧ ∀ i, U i i = 1 := hU
  obtain ⟨h1, h2⟩ := hU'
  rw [Matrix.det_of_upperTriangular (fun i j hij => h1 i j hij)]
  simp [h2]

lemma adj_of_inv {m : ℕ} {U V : Matrix (Fin m) (Fin m) ℂ} (hd : U.det = 1) (hVU : U * V = 1) :
    U.adjugate = V := by
  calc U.adjugate = U.adjugate * (U * V) := by rw [hVU, Matrix.mul_one]
    _ = (U.adjugate * U) * V := by rw [Matrix.mul_assoc]
    _ = V := by rw [Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul]

lemma zhat_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (y : B.Mat k r) :
    Zhat k r z z' (n * y * n') = (C2.uMap k r z n⁻¹)ᴴ * Zhat k r z z' y * C2.uMap k r z' n' := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hni := Nc.inv_mem n hn
  have h := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' hz hz' n⁻¹ ⟨1, one_mem_UW z, n⁻¹, hni, (one_mul _).symm⟩
    n' ⟨1, one_mem_UW z', n', hn', (one_mul _).symm⟩ y
  rwa [Matrix.nonsing_inv_nonsing_inv n (Nc.unit n hn)] at h

lemma uMap_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    C2.uMap k r z n * C2.uMap k r z n⁻¹ = 1 ∧ C2.uMap k r z n⁻¹ * C2.uMap k r z n = 1 := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hni := Nc.inv_mem n hn
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hS : n ∈ Sset k r z := ⟨1, one_mem_UW z, n, hn, (one_mul _).symm⟩
  have hSi : n⁻¹ ∈ Sset k r z := ⟨1, one_mem_UW z, n⁻¹, hni, (one_mul _).symm⟩
  have h1 : C2.uMap k r z 1 = 1 := hF.2 1 (one_mem_UW z)
  constructor
  · rw [← (hF.1 n hS).2.2 n⁻¹ hSi, Matrix.mul_nonsing_inv _ (Nc.unit n hn), h1]
  · rw [← (hF.1 n⁻¹ hSi).2.2 n hS, Matrix.nonsing_inv_mul _ (Nc.unit n hn), h1]

lemma key_alg {U' Zt Z Vm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU'adj : U' * U'.adjugate = 1)
    (hadj : Zt.adjugate = U'.adjugate * (Z.adjugate * Vmᴴ)) (hV : Vm ∈ C2.UTset (r + 1)) (c : Fin (r + 1)) :
    ∑ b, U' c b * Zt.adjugate b (Fin.last r) = Z.adjugate c (Fin.last r) := by
  have hV' : (∀ i j : Fin (r + 1), j < i → Vm i j = 0) ∧ ∀ i, Vm i i = 1 := hV
  obtain ⟨hV1, hV2⟩ := hV'
  have h1 : ∑ b, U' c b * Zt.adjugate b (Fin.last r) = (U' * Zt.adjugate) c (Fin.last r) :=
    (Matrix.mul_apply).symm
  rw [h1, hadj, ← Matrix.mul_assoc, hU'adj, Matrix.one_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp [Matrix.conjTranspose_apply, hV2]
  · intro d _ hd
    have hlt : d < Fin.last r := lt_of_le_of_ne (Fin.le_last d) hd
    simp [Matrix.conjTranspose_apply, hV1 _ _ hlt]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma regroup (M : B.Mat k r) (A C : Fin (r + 1) → ℂ) (U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (f : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (h : ∀ c, ∑ b, U' c b * A b = C c) :
    ∑ b, A b • (M *ᵥ ∑ c, U' c b • f c) = M *ᵥ ∑ c, C c • f c := by
  calc ∑ b, A b • (M *ᵥ ∑ c, U' c b • f c) = ∑ b, ∑ c, (U' c b * A b) • (M *ᵥ f c) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mv_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mulVec_smul, smul_smul, mul_comm (A b) (U' c b)]
    _ = ∑ c, ∑ b, (U' c b * A b) • (M *ᵥ f c) := Finset.sum_comm
    _ = ∑ c, C c • (M *ᵥ f c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_smul, h c]
    _ = M *ᵥ ∑ c, C c • f c := by
        rw [mv_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mulVec_smul]

theorem xcof_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (y : B.Mat k r) :
    xcof k r z z' (n * y * n') = n *ᵥ xcof k r z z' y := by
  have hF' := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hS : n ∈ Sset k r z := ⟨1, one_mem_UW z, n, hn, (one_mul _).symm⟩
  have hS' : n' ∈ Sset k r z' := ⟨1, one_mem_UW z', n', hn', (one_mul _).symm⟩
  have hV := (hF.1 n hS).2.1
  have hU' := (hF'.1 n' hS').2.1
  have hVU := (uMap_inv hz hn).1
  have hdU : ((C2.uMap k r z n⁻¹)ᴴ).det = 1 := by
    rw [Matrix.det_conjTranspose]
    have : (C2.uMap k r z n⁻¹).det * (C2.uMap k r z n).det = 1 := by
      rw [← Matrix.det_mul, (uMap_inv hz hn).2, Matrix.det_one]
    rw [unitri_det hV, mul_one] at this
    rw [this, star_one]
  have hadjU : ((C2.uMap k r z n⁻¹)ᴴ).adjugate = (C2.uMap k r z n)ᴴ :=
    adj_of_inv hdU (by rw [← Matrix.conjTranspose_mul, hVU, Matrix.conjTranspose_one])
  have hU'adj : C2.uMap k r z' n' * (C2.uMap k r z' n').adjugate = 1 := by
    rw [Matrix.mul_adjugate, unitri_det hU', one_smul]
  have hadj : (Zhat k r z z' (n * y * n')).adjugate =
      (C2.uMap k r z' n').adjugate * ((Zhat k r z z' y).adjugate * (C2.uMap k r z n)ᴴ) := by
    rw [zhat_N hz hz' hn hn' y, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjU]
  have hfr : ∀ b, n' *ᵥ fvec k r z' b = ∑ c, C2.uMap k r z' n' c b • fvec k r z' c := (hF'.1 n' hS').1
  unfold xcof
  have e1 : ∀ b, (n * y * n') *ᵥ fvec k r z' b = (n * y) *ᵥ ∑ c, C2.uMap k r z' n' c b • fvec k r z' c := by
    intro b; rw [← hfr b, mulVec_mulVec]
  simp only [e1]
  rw [regroup (n * y) _ _ _ _ (key_alg hU'adj hadj hV), ← mulVec_mulVec, mv_sum y]
  simp only [mulVec_smul]


end om

end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section om2

variable {k r : ℕ}

lemma adjugate_last_entry_sum {U' W' Zt Z Vm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hW : U'.adjugate = W')
    (hW' : W' ∈ C2.UTset (r + 1)) (hadj : Zt.adjugate = U'.adjugate * (Z.adjugate * Vmᴴ)) (a : Fin (r + 1)) :
    Zt.adjugate (Fin.last r) a = ∑ e, Z.adjugate (Fin.last r) e * star (Vm a e) := by
  rw [hadj, hW, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
  · rw [hW'.2, one_mul, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
  · intro e _ he
    rw [hW'.1 _ _ (lt_of_le_of_ne (Fin.le_last e) he), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem xcofL_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (y : B.Mat k r) :
    xcofL k r z z' (n * y * n') = n *ᵥ xcofL k r z z' y := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hF' := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hS : n ∈ Sset k r z := ⟨1, one_mem_UW z, n, hn, (one_mul _).symm⟩
  have hSi' : n'⁻¹ ∈ Sset k r z' := ⟨1, one_mem_UW z', n'⁻¹, Nc.inv_mem n' hn', (one_mul _).symm⟩
  have hS' : n' ∈ Sset k r z' := ⟨1, one_mem_UW z', n', hn', (one_mul _).symm⟩
  have hV := (hF.1 n hS).2.1
  have hU' := (hF'.1 n' hS').2.1
  have hW' := (hF'.1 n'⁻¹ hSi').2.1
  have hVU := (uMap_inv hz hn).1
  have hdU : ((C2.uMap k r z n⁻¹)ᴴ).det = 1 := by
    rw [Matrix.det_conjTranspose]
    have : (C2.uMap k r z n⁻¹).det * (C2.uMap k r z n).det = 1 := by
      rw [← Matrix.det_mul, (uMap_inv hz hn).2, Matrix.det_one]
    rw [unitri_det hV, mul_one] at this
    rw [this, star_one]
  have hadjU : ((C2.uMap k r z n⁻¹)ᴴ).adjugate = (C2.uMap k r z n)ᴴ :=
    adj_of_inv hdU (by rw [← Matrix.conjTranspose_mul, hVU, Matrix.conjTranspose_one])
  have hW : (C2.uMap k r z' n').adjugate = C2.uMap k r z' n'⁻¹ := adj_of_inv (unitri_det hU') (uMap_inv hz' hn').1
  have hadj : (Zhat k r z z' (n * y * n')).adjugate =
      (C2.uMap k r z' n').adjugate * ((Zhat k r z z' y).adjugate * (C2.uMap k r z n)ᴴ) := by
    rw [zhat_N hz hz' hn hn' y, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjU]
  have hfr : ∀ e, n *ᵥ fvec k r z e = ∑ a, C2.uMap k r z n a e • fvec k r z a := (hF.1 n hS).1
  unfold xcofL
  simp only [adjugate_last_entry_sum hW hW' hadj, star_sum, star_mul', star_star]
  rw [mv_sum]
  simp only [mulVec_smul, hfr, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

lemma ginv_xcofL_esI (z z' : Fin (2 * r + k + 1) → ℂ) {y : B.Mat k r} (hy : y ∈ B.GV k r) (a : Fin r) :
    (y⁻¹ *ᵥ xcofL k r z z' y) (esI k r a) = 0 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  have hu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
  rw [← herm_bvec_eI (y⁻¹ *ᵥ xcofL k r z z' y) a, ← fvec_lt z' a,
    ← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, one_mulVec,
    hm_symm _ hH]
  unfold xcofL
  rw [hm_sum_r]
  have := adj_row (Zhat k r z z' y) ⟨a.val, by omega⟩ (by
    intro h; have := congrArg Fin.val h; simp at this; omega)
  simp only [star_star]
  rw [show (∑ i, (Zhat k r z z' y).adjugate (Fin.last r) i *
      herm (Hpk k r) (y *ᵥ fvec k r z' ⟨a.val, by omega⟩) (fvec k r z i)) = 0 from this, star_zero]



end om2

end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def StabCore : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z',
      α *ᵥ D0.nu = D0.nu → β⁻¹ *ᵥ D0.nu' = D0.nu' →
      α * y * β ∈ gfSig D0 → Rel z z' y (α * y * β)

section eqv

variable {k r : ℕ}

lemma uw_entry {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) (h : ¬ (r ≤ i.val ∧ i.val ≤ r + k) ∨ ¬ (r ≤ j.val ∧ j.val ≤ r + k)) :
    α i j = if i = j then 1 else 0 := by
  obtain ⟨μ, _, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWset_iff hz α).1 hα
  rcases h with h | h
  · exact Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_out_row μ i j h
  · exact Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_out_col μ i j h

lemma wb_UW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    (v : Fin (2 * r + k + 1) → ℂ) :
    PI.UnitaryGroupMassFormula.GsFr.wbPart k r (α *ᵥ v) = α *ᵥ PI.UnitaryGroupMassFormula.GsFr.wbPart k r v := by
  funext i
  unfold PI.UnitaryGroupMassFormula.GsFr.wbPart
  simp only [mulVec, dotProduct]
  split_ifs with hi
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · rw [uw_entry hz hα i j (Or.inr hj), if_neg (fun (e : i = j) => hj (e ▸ hi)), zero_mul, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [uw_entry hz hα i j (Or.inl hi)]
    split_ifs with h1 h2
    · subst h1; exact absurd h2 hi
    · simp
    · simp
    · simp

lemma prW_UW {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    (v : Fin (2 * r + k + 1) → ℂ) : prW k r z (α *ᵥ v) = α *ᵥ prW k r z v := by
  have hUz := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1 (PI.UnitaryGroupMassFormula.GsFr.wbPart k r v) z
  rw [hα.2.2] at hUz
  unfold prW
  rw [wb_UW hz.1 hα, hUz, mulVec_add, mulVec_smul, hα.2.2]

lemma uw_fvec {z : Fin (2 * r + k + 1) → ℂ} {α : B.Mat k r} (hα : α ∈ UWset k r z) (b : Fin (r + 1)) :
    α *ᵥ fvec k r z b = fvec k r z b := by
  unfold fvec
  split_ifs with h
  · exact (hα.2.1 ⟨b.val, h⟩).1
  · exact hα.2.2

lemma zhat_UW {z z' : Fin (2 * r + k + 1) → ℂ} {α β : B.Mat k r} (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z')
    (y : B.Mat k r) : Zhat k r z z' (α * y * β) = Zhat k r z z' y := by
  funext a b
  simp only [Zhat]
  rw [← mulVec_mulVec, uw_fvec hβ, ← mulVec_mulVec]
  conv_lhs => rw [← uw_fvec hα a]
  rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]

lemma xcof_UW {z z' : Fin (2 * r + k + 1) → ℂ} {α β : B.Mat k r} (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z')
    (y : B.Mat k r) : xcof k r z z' (α * y * β) = α *ᵥ xcof k r z z' y := by
  unfold xcof
  rw [zhat_UW hα hβ, mv_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mulVec_smul, ← mulVec_mulVec, uw_fvec hβ, ← mulVec_mulVec]

lemma xcofL_UW {z z' : Fin (2 * r + k + 1) → ℂ} {α β : B.Mat k r} (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z')
    (y : B.Mat k r) : xcofL k r z z' (α * y * β) = xcofL k r z z' y := by
  unfold xcofL; rw [zhat_UW hα hβ]

lemma xcofL_fix {z z' : Fin (2 * r + k + 1) → ℂ} {α : B.Mat k r} (hα : α ∈ UWset k r z) (y : B.Mat k r) :
    α *ᵥ xcofL k r z z' y = xcofL k r z z' y := by
  unfold xcofL
  rw [mv_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [mulVec_smul, uw_fvec hα]

theorem omW_UW {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {α β : B.Mat k r} (hα : α ∈ UWset k r z)
    (hβ : β ∈ UWset k r z') (y : B.Mat k r) : omW k r z z' (α * y * β) = α *ᵥ omW k r z z' y := by
  unfold omW; rw [xcof_UW hα hβ, prW_UW hz hα]

theorem omW'_UW {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {α β : B.Mat k r}
    (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z') (y : B.Mat k r) :
    omW' k r z z' (α * y * β) = β⁻¹ *ᵥ omW' k r z z' y := by
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  unfold omW'
  rw [xcofL_UW hα hβ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec,
    xcofL_fix (Wz.inv_mem α hα), prW_UW hz' (Wz'.inv_mem β hβ)]


end eqv


end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def IsoCore : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z',
      α *ᵥ D0.nu = D0.nu → β⁻¹ *ᵥ D0.nu' = D0.nu' → (∀ u ∈ D0.U0, α *ᵥ (β *ᵥ u) = u) →
      ∃ m ∈ C2.N0set k r z, ∃ m' ∈ C2.N0set k r z', α * (m⁻¹ * y * m') * β = y

section aux

variable {k r : ℕ}

lemma uw_X {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xsp k r) : α *ᵥ v = v := by
  have hα' := hα
  unfold UWset at hα'
  simp only [Set.mem_setOf_eq] at hα'
  obtain ⟨-, hfix, -⟩ := hα'
  unfold Xsp at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact (hfix a).1
  | zero => exact Matrix.mulVec_zero α
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
  | smul c x _ hx => rw [Matrix.mulVec_smul, hx]

lemma uw_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (α *ᵥ u) := by
  have hα' := hα
  unfold UWset at hα'
  simp only [Set.mem_setOf_eq] at hα'
  obtain ⟨hU, hfix, -⟩ := hα'
  unfold UH at hU
  simp only [Set.mem_setOf_eq] at hU
  have key : ∀ x w : Fin (2 * r + k + 1) → ℂ,
      star (α *ᵥ w) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ x)) = star w ⬝ᵥ (Hpk k r *ᵥ x) := by
    intro x w
    rw [Matrix.star_mulVec, ← dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, hU]
  have hstar : ∀ (w : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)),
      star w ⬝ᵥ Pi.single j 1 = star (w j) := by
    intro w j
    rw [dotProduct_single, mul_one]
    rfl
  have hHe : ∀ a : Fin r, Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
    intro a
    have ha := a.isLt
    funext i
    have hi := i.isLt
    unfold Hpk bvec eI esI
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_mk]
    split_ifs <;> first | rfl | omega | (simp only [Fin.ext_iff, Fin.val_mk] at *; omega)
  have hHe' : ∀ a : Fin r, Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
    intro a
    have ha := a.isLt
    funext i
    have hi := i.isLt
    unfold Hpk bvec eI esI
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_mk]
    split_ifs <;> first | rfl | omega | (simp only [Fin.ext_iff, Fin.val_mk] at *; omega)
  intro i hi
  have hsi : star ((α *ᵥ u) i) = 0 := by
    rcases hi with hi | hi
    · have he : bvec (eI k r ⟨i, hi⟩) = Pi.single i 1 := by
        unfold bvec eI
        rfl
      calc star ((α *ᵥ u) i) = star (α *ᵥ u) ⬝ᵥ Pi.single i 1 := (hstar _ _).symm
        _ = star (α *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ bvec (esI k r ⟨i, hi⟩))) := by
          rw [(hfix _).2, hHe, he]
        _ = star u ⬝ᵥ (Hpk k r *ᵥ bvec (esI k r ⟨i, hi⟩)) := key _ _
        _ = star (u i) := by rw [hHe, he, hstar]
        _ = 0 := by rw [hu i (Or.inl hi), star_zero]
    · have hi2 := i.isLt
      have h' : 2 * r + k - (i : ℕ) < r := by omega
      have he : bvec (esI k r ⟨2 * r + k - i, h'⟩) = Pi.single i 1 := by
        unfold bvec esI
        dsimp only
        congr 1
        ext
        simp only [Fin.val_mk]
        omega
      calc star ((α *ᵥ u) i) = star (α *ᵥ u) ⬝ᵥ Pi.single i 1 := (hstar _ _).symm
        _ = star (α *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ bvec (eI k r ⟨2 * r + k - i, h'⟩))) := by
          rw [(hfix _).1, hHe', he]
        _ = star u ⬝ᵥ (Hpk k r *ᵥ bvec (eI k r ⟨2 * r + k - i, h'⟩)) := key _ _
        _ = star (u i) := by rw [hHe', he, hstar]
        _ = 0 := by rw [hu i (Or.inr hi), star_zero]
  exact star_eq_zero.mp hsi

lemma herm_X_wb {x z : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hz : inWb k r z) : herm (Hpk k r) x z = 0 := by
  unfold Xsp at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    unfold herm
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) < r ∨ r + k < (i : ℕ)
    · simp [hz i hi]
    · push_neg at hi
      have ha := a.isLt
      have hsum : (Hpk k r *ᵥ bvec (eI k r a)) i = 0 := by
        unfold Hpk bvec eI
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_mk]
        split_ifs <;> first | rfl | (simp only [Fin.ext_iff, Fin.val_mk] at *; omega) | omega
      simp [hsum]
  | zero =>
    unfold herm
    rw [Matrix.mulVec_zero, dotProduct_zero]
  | add x y _ _ hx hy =>
    unfold herm at *
    rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
  | smul c x _ hx =>
    unfold herm at *
    rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]

lemma X_wb_zero {v : Fin (2 * r + k + 1) → ℂ} (hX : v ∈ Xsp k r) (hW : inWb k r v) : v = 0 := by
  have hlow : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → v i = 0 := by
    clear hW
    unfold Xsp at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro i hi
      unfold bvec eI
      dsimp only
      rw [Pi.single_apply, if_neg]
      intro h
      have h1 := congrArg Fin.val h
      simp only [Fin.val_mk] at h1
      have := a.isLt
      omega
    | zero =>
      intro i _
      rfl
    | add x y _ _ hx hy =>
      intro i hi
      simp [hx i hi, hy i hi]
    | smul c x _ hx =>
      intro i hi
      simp [hx i hi]
  funext i
  by_cases hi : (i : ℕ) < r
  · exact hW i (Or.inl hi)
  · exact hlow i (by omega)

lemma det_ne_of_G {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hG : 0 < Gf k r z z' y) : (Zhat k r z z' y).det ≠ 0 := by
  have hD : Dmin k r z z' y (Fin.last (r + 1)) ≠ 0 := by
    intro h
    unfold Gf at hG
    rw [h, map_zero] at hG
    have := mul_nonneg (mul_nonneg hz.2.le hz'.2.le) (Complex.normSq_nonneg (Dmin k r z z' y ⟨r, by omega⟩))
    linarith
  unfold Dmin at hD
  have hid : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) : Fin (r + 1) → Fin (r + 1)) = id :=
    funext fun i => Fin.ext rfl
  rwa [hid, Matrix.submatrix_id_id] at hD

lemma lift_unique {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hG : 0 < Gf k r z z' y) {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r)
    (horth : ∀ a, herm (Hpk k r) (y *ᵥ x) (fvec k r z a) = 0) : x = 0 := by
  have hx' := (mem_Xsp_iff x).1 hx
  set c : Fin (r + 1) → ℂ := fun b => if h : b.val < r then x (eI k r ⟨b.val, h⟩) else 0 with hc
  have ex : x = ∑ b, c b • fvec k r z' b := by
    funext i
    rw [Finset.sum_apply]
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
      · have e1 : eI k r ⟨i.val, hi⟩ = i := Fin.ext (by simp [eI])
        simp [hc, hi, fvec, e1, bvec]
      · intro b _ hb
        simp only [Pi.smul_apply, smul_eq_mul, hc]
        split_ifs with h
        · have : i ≠ eI k r ⟨b.val, h⟩ := by
            intro e; apply hb; apply Fin.ext; have := congrArg Fin.val e; simp [eI] at this ⊢; omega
          simp [fvec, h, bvec, this]
        · simp
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [hx' i (by omega)]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, hc]
      split_ifs with h
      · have : i ≠ eI k r ⟨b.val, h⟩ := by
          intro e; have := congrArg Fin.val e; simp [eI] at this; omega
        simp [fvec, h, bvec, this]
      · simp
  have hZc : Zhat k r z z' y *ᵥ c = 0 := by
    funext a
    have := horth a
    rw [ex, mv_sum] at this
    simp only [mulVec_smul] at this
    rw [hm_sum_l] at this
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by simp only [Zhat]; ring
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero (det_ne_of_G hz hz' hG) hZc
  rw [ex, hc0]
  simp

end aux



end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section iso

variable {k r : ℕ}

lemma herm_X_gen {x w : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hw : ∀ i : Fin (2 * r + k + 1), r + k < i.val → w i = 0) :
    herm (Hpk k r) x w = 0 := by
  have hlo : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → x j = 0 := by
    intro j hj
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      have hne : j ≠ eI k r a := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, Pi.single_apply, hne]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ j.val
  · rw [hlo j hj, mul_zero, mul_zero]
  · push_neg at hj
    by_cases hi : r + k < i.val
    · rw [hw i hi, star_zero, zero_mul]
    · push_neg at hi
      have hH : Hpk k r i j = 0 := by
        unfold Hpk
        simp only [Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hH, zero_mul, mul_zero]

lemma herm_wb_X {x w : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hw : ∀ i : Fin (2 * r + k + 1), r + k < i.val → w i = 0) :
    herm (Hpk k r) w x = 0 := by
  have hlo : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → x j = 0 := by
    intro j hj
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      have hne : j ≠ eI k r a := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, Pi.single_apply, hne]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hi : r ≤ i.val
  · rw [hlo i hi, star_zero, zero_mul]
  · push_neg at hi
    by_cases hj : r + k < j.val
    · rw [hw j hj, mul_zero, mul_zero]
    · push_neg at hj
      have hH : Hpk k r i j = 0 := by
        unfold Hpk
        simp only [Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hH, zero_mul, mul_zero]

lemma X_hi {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → x i = 0 := by
  intro i hi
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have hne : i ≠ eI k r a := by
      intro h
      have := congrArg Fin.val h
      simp [eI] at this
      omega
    simp [bvec, Pi.single_apply, hne]
  | zero => rfl
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

lemma wb_hi {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → x i = 0 := by
  intro i hi
  exact hx i (Or.inr hi)

lemma fix_X {g : B.Mat k r} (hg : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a)) {x : Fin (2 * r + k + 1) → ℂ}
    (hx : x ∈ Xsp k r) : g *ᵥ x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact hg a
  | zero => exact Matrix.mulVec_zero g
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy]

lemma uw_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {nu : Fin (2 * r + k + 1) → ℂ} {U0 : Set (Fin (2 * r + k + 1) → ℂ)}
    (hnu : nu ∈ Wsp k r z) (hnu1 : herm (Hpk k r) nu nu = 1)
    (hU0 : ∀ u, u ∈ U0 ↔ u ∈ Wsp k r z ∧ herm (Hpk k r) u nu = 0)
    {h α : B.Mat k r} (hh : h ∈ UWset k r z) (hα : α ∈ UWset k r z)
    (hU : ∀ u ∈ U0, h *ᵥ u = α *ᵥ u) (hn : h *ᵥ nu = α *ᵥ nu) : h = α := by
  obtain ⟨hzW, hTz⟩ := hz
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro h0
    unfold Formalism.QuantumDeterminants.Tz at hTz
    rw [h0] at hTz
    simp at hTz
  have hlin_sub : ∀ a b w, herm (Hpk k r) (a - b) w = herm (Hpk k r) a w - herm (Hpk k r) b w := by
    intro a b w
    simp [herm, Matrix.mulVec_sub, dotProduct_sub]
  have hlin_smul : ∀ (c : ℂ) a w, herm (Hpk k r) (c • a) w = c * herm (Hpk k r) a w := by
    intro c a w
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  have hW : ∀ v, inWb k r v → h *ᵥ v = α *ᵥ v := by
    intro v hv
    obtain ⟨d, hd⟩ : ∃ d, d = herm (Hpk k r) v z / herm (Hpk k r) z z := ⟨_, rfl⟩
    have hv'W : inWb k r (v - d • z) := fun i hi => by simp [hv i hi, hzW i hi]
    have hv'z : herm (Hpk k r) (v - d • z) z = 0 := by
      rw [hlin_sub, hlin_smul, hd, div_mul_cancel₀ _ hzz, sub_self]
    obtain ⟨c, hc⟩ : ∃ c, c = herm (Hpk k r) (v - d • z) nu := ⟨_, rfl⟩
    have hu : (v - d • z) - c • nu ∈ U0 := by
      rw [hU0]
      refine ⟨⟨fun i hi => by simp [hv'W i hi, hnu.1 i hi], ?_⟩, ?_⟩
      · rw [hlin_sub, hlin_smul, hv'z, hnu.2, mul_zero, sub_zero]
      · rw [hlin_sub, hlin_smul, hnu1, mul_one, hc, sub_self]
    have hv_dec : v = ((v - d • z) - c • nu) + c • nu + d • z := by abel
    rw [hv_dec, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hU _ hu, hn, hh.2.2,
      hα.2.2]
  have hcol : ∀ j : Fin (2 * r + k + 1), h *ᵥ Pi.single j 1 = α *ᵥ Pi.single j 1 := by
    intro j
    by_cases hj1 : j.val < r
    · have e : (Pi.single j (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = bvec (eI k r ⟨j.val, hj1⟩) := by
        show Pi.single j 1 = Pi.single (eI k r ⟨j.val, hj1⟩) 1
        congr 1
      rw [e, (hh.2.1 _).1, (hα.2.1 _).1]
    · by_cases hj2 : r + k < j.val
      · have hlt := j.isLt
        have e : (Pi.single j (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) =
            bvec (esI k r ⟨2 * r + k - j.val, by omega⟩) := by
          show Pi.single j 1 = Pi.single (esI k r ⟨2 * r + k - j.val, by omega⟩) 1
          congr 1
          exact Fin.ext (by simp only [esI]; omega)
        rw [e, (hh.2.1 _).2, (hα.2.1 _).2]
      · apply hW
        intro i hi
        have hne : i ≠ j := by
          intro hij
          subst hij
          omega
        simp [Pi.single_apply, hne]
  ext i j
  have h1 := congrFun (hcol j) i
  simpa [Matrix.mulVec_single_one] using h1

end iso

end PI.UnitaryGroupMassFormula.GsFr
end
end
