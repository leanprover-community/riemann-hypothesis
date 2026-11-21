import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix

namespace Formalism.FourierDecayAlt.P.Jx6

theorem psd_mul {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : TB.PSDOn F (fun x y => k x y * k' x y) := by
  unfold TB.PSDOn at *
  exact hk.hadamard hk'

theorem psd_pull {α β : Type} {G : Finset β} {F : Finset α} (f : G → F) {k : α → α → ℂ}
    {k' : β → β → ℂ} (h : ∀ x y : G, k' x y = k (f x) (f y)) (hk : TB.PSDOn F k) : TB.PSDOn G k' := by
  unfold TB.PSDOn at *
  have e : (Matrix.of fun x y : G => k' x y) = (Matrix.of fun x y : F => k x y).submatrix f f := by
    ext x y; exact h x y
  rw [e]; exact hk.submatrix f

theorem quadM {α : Type} (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    star (fun x : F => a x) ⬝ᵥ (Matrix.of fun x y : F => k x y) *ᵥ (fun x : F => a x) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort F (fun x => ∑ y ∈ F, conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_coe_sort F (fun y => conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro y _
  simp only [RCLike.star_def]; ring

theorem sum_nonneg_of_psd {α : Type} {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) :
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y).re := by
  unfold TB.PSDOn at hk
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hk
  have h := hk.2 (fun x : F => (fun _ : α => (1 : ℂ)) x)
  rw [quadM F k (fun _ => 1)] at h
  have h2 := (Complex.le_def.1 h).1
  simpa using h2

theorem sum_mul_nonneg {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : 0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y * k' x y).re :=
  sum_nonneg_of_psd (psd_mul hk hk')

theorem maj_mono {E W : Type} [Field E] (D : TB.Data E W) (ρ ρ' : Fin D.f → ℝ) (l : E)
    (h : ∀ v, 0 ≤ ρ v ∧ ρ v ≤ ρ' v) (hav : ∀ v, 0 ≤ D.av v l) : D.maj ρ l ≤ D.maj ρ' l := by
  unfold TB.Data.maj
  apply Finset.prod_le_prod
  · intro v _
    exact le_min zero_le_one (pow_nonneg (div_nonneg (h v).1 (hav v)) _)
  · intro v _
    exact min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg (h v).1 (hav v))
      (div_le_div_of_nonneg_right (h v).2 (hav v)) _)

theorem baseGram_nonneg {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ := by
  unfold TB.Data.N0
  exact div_nonneg (sum_mul_nonneg hκ (hG ε hε k w Y)) (hW w).le

theorem Nst_nonneg {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) (t : E) : 0 ≤ (D.Nst ε i s w Y κ t t).re := by
  classical
  unfold TB.Data.Nst
  rw [Complex.div_ofReal_re]
  refine div_nonneg (sum_mul_nonneg hκ ?_) (hW w).le
  have hm : ∀ x ∈ Y, TB.join x s t ∈ Y.image (fun h => TB.join h s t) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  exact psd_pull (F := Y.image (fun h => TB.join h s t))
    (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) (hG ε hε i w _)

theorem blk_psd {E : Type} [Field E] {Y : Finset (TB.Pt E)} {S : Finset E} {s : ℕ}
    {κ : TB.Pt E → TB.Pt E → ℂ} (hκ : TB.PSDOn (TB.pts Y s S) κ) {t : E} (ht : t ∈ S) :
    TB.PSDOn Y (TB.blk κ s t t) := by
  classical
  have hm : ∀ x ∈ Y, TB.join x s t ∈ TB.pts Y s S := by
    intro x hx
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(x, t), Finset.mem_product.2 ⟨hx, ht⟩, rfl⟩
  exact psd_pull (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) hκ

end Formalism.FourierDecayAlt.P.Jx6

namespace Formalism.FourierDecayAlt.P

open Jx6







theorem form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by
  intro hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩ := hPos
  have hn : 0 < B.n0c := a33
  have hen : 0 < B.e1 * B.n0c := mul_pos he hn
  have key := hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) }
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF
    (by
      constructor
      · show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))
        rw [mul_div_cancel₀ _ hen.ne']
      · show 0 ≤ B.KV / (B.e1 * B.n0c)
        exact div_nonneg hKV hen.le)
    hMass
    (by show B.e1 ≤ B.e1; exact le_refl _)
    (by
      show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN
      rw [← mul_div_assoc, div_le_iff₀ hen]
      have e : (1 + B.δ) * B.e1 * (B.n0c * B.IntN) = (1 + B.δ) * B.IntN * (B.e1 * B.n0c) := by ring
      linarith)
    hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  exact key

end Formalism.FourierDecayAlt.P
