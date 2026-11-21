import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusMatchPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Pin1b

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem pin1 (hx : (U.X k).IsOrtho x.1) (a' : (W.F.Di (W.ik k)).La) :
    A.φ ((W.φ k a' : (U.X k).Λ) : Fin r → E) = Lmap hU hσ W A (star (W.Pm a')) := by
  obtain ⟨v, hv⟩ : ∃ v : Fin r → E, v = ((W.φ k a' : (U.X k).Λ) : Fin r → E) := ⟨_, rfl⟩
  rw [← hv]
  have hdet : ∀ τ : (U.X k).Ψ, (mat x.1 τ).det ≠ 0 := fun τ => (x.2 τ).1
  have hrel : ∀ ρ : E →+* ℂ, relab c σ ((relabE c σ).symm (conjEmb ρ)) = conjEmb ρ :=
    fun ρ => (relabE c σ).apply_symm_apply _
  ext ⟨ρ, a⟩
  rw [Lmap_apply, Pi.star_apply, W.pm_eq, letT_e, ← hv]
  simp only [hrel]
  rw [fibE_val]
  by_cases h : ρ ∈ (U.X k).Ψ
  · rw [if_pos h]
    have ha := index_lt_signature_of_mem hU A h a
    rw [perFr_conj (U.X k) x.1 v h _ (by omega)]
    have e1 := A.coord_pos ⟨ρ, h⟩ a v
    refine e1.trans ?_
    rw [e_mul A hx hdet]
    rw [ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_smul_right, wt, dif_pos h, star_def,
      ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_conj ρ (U.X k).Gm (U.X k).Gm_herm]
    have hidx : (⟨(U.X k).p0 - 1 - ((U.X k).p0 - 1 - (a : ℕ)), by have := (U.X k).p0_le; omega⟩ : Fin r) =
        Fin.castLE (by rw [A.dim_pos ⟨ρ, h⟩]; exact (U.X k).p0_le) a := Fin.ext (by simp; omega)
    rw [hidx]
    have hcast : ∀ (h1 : A.T.dim ρ ≤ r), Fin.castLE h1 a = ⟨a, lt_of_lt_of_le a.2 h1⟩ := fun _ => rfl
    simp only [yf, hcast]
    ring
  · rw [if_neg h]
    obtain ⟨τ, rfl⟩ : ∃ τ, conjEmb τ = ρ := ⟨conjEmb ρ, conjEmb_conjEmb ρ⟩
    have hτ : conjEmb (conjEmb τ) ∈ (U.X k).Ψ := (conj_mem_iff _).mpr h
    have hτ' : τ ∈ (U.X k).Ψ := by rwa [conjEmb_conjEmb] at hτ
    have ha := index_lt_complementSignature_of_not_mem hU A h a
    have hp := (U.X k).p0_le
    rw [perFr_self (U.X k) x.1 v hτ a (by omega), inv_coord (U.X k) x.1 hx _ (hdet _) (Data.emb _ v), wt, dif_neg h]
    have hsub : (⟨conjEmb (conjEmb τ), hτ⟩ : (U.X k).Ψ) = ⟨τ, hτ'⟩ := Subtype.ext (conjEmb_conjEmb τ)
    simp only [hsub]
    rw [conjEmb_conjEmb]
    have e1 := A.coord_neg ⟨τ, hτ'⟩ a v
    refine e1.trans ?_
    rw [e_mul A hx hdet, ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_smul_right]
    have hs : (sgn (U.X k).p0 ((U.X k).p0 + (a : ℕ)) : ℂ) = -1 := by
      unfold sgn
      rw [if_neg (by omega)]
      norm_num
    simp only [yf, star_def, map_neg, map_mul, Complex.conj_conj, hs, map_one]
    ring

end Pin1b

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexConjugate

namespace Pin2

theorem star_real_smul {g : ℕ} (t : ℝ) (v : Fin g → ℂ) : star ((t : ℂ) • v) = (t : ℂ) • star v := by
  ext i
  simp

theorem form_zero {g : ℕ} (D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (addL : ∀ z z' w, D (z + z') w = D z w + D z' w) (smulL : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (addR : ∀ z w w', D z (w + w') = D z w + D z w') (smulR : ∀ (t : ℝ) z w, D z ((t : ℂ) • w) = t * D z w)
    (h0 : ∀ p ∈ S, ∀ q ∈ S, (D (star p) (star q)).im = 0) (z w : Fin g → ℂ) : D z w = 0 := by
  have hrs : ∀ (t : ℝ) (u : Fin g → ℂ), t • u = (t : ℂ) • u := fun t u => by
    ext i
    simp [Complex.real_smul]
  have hstar_smul : ∀ (t : ℝ) (u : Fin g → ℂ), star (t • u) = t • star u := fun t u => by
    rw [hrs, hrs, star_real_smul]
  have hD0 : ∀ u, D 0 u = 0 := fun u => by simpa using smulL 0 0 u
  have hD0' : ∀ u, D u 0 = 0 := fun u => by simpa using smulR 0 u 0

  let N1 : Submodule ℝ (Fin g → ℂ) :=
    { carrier := {u | ∀ q ∈ S, (D (star u) (star q)).im = 0}
      add_mem' := by
        intro a b ha hb q hq
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [star_add, addL, Complex.add_im, ha q hq, hb q hq, add_zero]
      zero_mem' := by
        intro q _
        rw [star_zero, hD0, Complex.zero_im]
      smul_mem' := by
        intro t a ha q hq
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hstar_smul, hrs, smulL, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha q hq, mul_zero,
          zero_mul, add_zero] }
  have hN1 : ∀ u, u ∈ N1 := by
    intro u
    have h : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ N1 := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      intro p hp
      show ∀ q ∈ S, _
      exact h0 p hp
    exact h Submodule.mem_top
  have h1 : ∀ u, ∀ q ∈ S, (D u (star q)).im = 0 := by
    intro u
    have hm : ∀ q ∈ S, (D (star (star u)) (star q)).im = 0 := hN1 (star u)
    rw [star_star] at hm
    exact hm

  let N2 : Submodule ℝ (Fin g → ℂ) :=
    { carrier := {q | ∀ u, (D u (star q)).im = 0}
      add_mem' := by
        intro a b ha hb u
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [star_add, addR, Complex.add_im, ha u, hb u, add_zero]
      zero_mem' := by
        intro u
        rw [star_zero, hD0', Complex.zero_im]
      smul_mem' := by
        intro t a ha u
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hstar_smul, hrs, smulR, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha u, mul_zero,
          zero_mul, add_zero] }
  have hN2 : ∀ q, q ∈ N2 := by
    intro q
    have h : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ N2 := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      intro p hp
      show ∀ u, _
      exact fun u => h1 u p hp
    exact h Submodule.mem_top
  have h2 : ∀ u q, (D u q).im = 0 := by
    intro u q
    have hm : ∀ u, (D u (star (star q))).im = 0 := hN2 (star q)
    rw [star_star] at hm
    exact hm u
  have hre : (D z w).re = 0 := by
    have h := h2 (Complex.I • z) w
    rw [smulL, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h
    exact h
  exact Complex.ext_iff.2 ⟨by simp [hre], by simp [h2 z w]⟩

section Hf

variable {ι : Type} [Fintype ι]

theorem hf_add_left (v v' w : EuclideanSpace ℂ ι) : Hf (v + v') w = Hf v w + Hf v' w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_add_right (v w w' : EuclideanSpace ℂ ι) : Hf v (w + w') = Hf v w + Hf v w' := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_smul_left (t : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (t • v) w = t * Hf v w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_real_smul_right (t : ℝ) (v w : EuclideanSpace ℂ ι) : Hf v ((t : ℂ) • w) = t * Hf v w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_re_nonneg (v : EuclideanSpace ℂ ι) : 0 ≤ (Hf v v).re := by
  unfold Hf
  simp [inner_self_nonneg]
  exact Finset.sum_nonneg fun x _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

end Hf

section HermForm

variable {g : ℕ}

theorem hm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_real_smul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z ((t : ℂ) • w) = t * hermForm Hm z w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

end HermForm

end Pin2

section Pin2

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem lattice_trace_imaginary_part (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (a b : (W.F.Di (W.ik k)).La) :
    (Hf (Lmap hU hσ W A (star (W.Pm a))) (Lmap hU hσ W A (star (W.Pm b)))).im =
        A.sg * ((Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm ((W.φ k a : (U.X k).Λ) : Fin r → E)
          ((W.φ k b : (U.X k).Λ) : Fin r → E)) : ℚ) : ℝ) ∧
      (star (hermForm Wu.Hm (star (star (W.Pm a))) (star (star (W.Pm b))))).im =
        ((Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm ((W.φ k a : (U.X k).Λ) : Fin r → E)
          ((W.φ k b : (U.X k).Λ) : Fin r → E)) : ℚ) : ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [← pin1 hU hσ W A hx a, ← pin1 hU hσ W A hx b]
    exact A.im_eq _ (W.φ k a).2 _ (W.φ k b).2
  · rw [star_star, star_star, Complex.star_def, Complex.conj_im, Wu.c1]
    have hi := W.isom k a b
    rw [neg_mul, map_neg] at hi
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hi
    push_cast at hr
    linarith

theorem pin2 (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (z z' : Fin W.g → ℂ) :
    Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') = star (hermForm Wu.Hm (star z) (star z')) := by
  have key : ∀ z z', Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') -
      (A.sg : ℂ) * star (hermForm Wu.Hm (star z) (star z')) = 0 := by
    intro z z'
    refine Pin2.form_zero (fun z z' => Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') -
        (A.sg : ℂ) * star (hermForm Wu.Hm (star z) (star z')))
      (Set.range W.Pm) W.per.2.2.2.1 ?_ ?_ ?_ ?_ ?_ z z'
    · intro z z' w
      simp only [map_add, Pin2.hf_add_left, star_add, Pin2.hm_add_left]
      ring
    · intro t z w
      simp only [map_smul, Pin2.hf_smul_left, star_smul, Pin2.hm_smul_left, star_mul', star_star]
      ring
    · intro z w w'
      simp only [map_add, Pin2.hf_add_right, star_add, Pin2.hm_add_right]
      ring
    · intro t z w
      simp only [map_smul, Pin2.hf_real_smul_right, Pin2.star_real_smul, Pin2.hm_real_smul_right, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      ring
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      obtain ⟨h1, h2⟩ := lattice_trace_imaginary_part hU hσ W A hx Wu a b
      show (Hf (Lmap hU hσ W A (star (W.Pm a))) (Lmap hU hσ W A (star (W.Pm b))) -
        (A.sg : ℂ) * star (hermForm Wu.Hm (star (star (W.Pm a))) (star (star (W.Pm b))))).im = 0
      rw [Complex.sub_im, Complex.im_ofReal_mul, h1, h2]
      ring
  rcases A.sg_pm with h | h
  · have := key z z'
    rw [h, Complex.ofReal_one, _root_.one_mul, sub_eq_zero] at this
    exact this
  · rcases Nat.eq_zero_or_pos W.g with hg | hg
    · have hz : ∀ v : Fin W.g → ℂ, v = 0 := fun v => funext fun i => absurd i.2 (by omega)
      rw [hz z, hz z', map_zero]
      simp [Hf, hermForm]
    · exfalso
      obtain ⟨v, hv⟩ : ∃ v : Fin W.g → ℂ, v = Pi.single (⟨0, hg⟩ : Fin W.g) 1 := ⟨_, rfl⟩
      have hv0 : star v ≠ 0 := by
        intro h0
        have := congrFun h0 ⟨0, hg⟩
        simp [hv] at this
      have hpos := Wu.pos (star v) hv0
      have hk := key v v
      rw [h, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, sub_neg_eq_add] at hk
      have hre := congrArg Complex.re hk
      rw [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at hre
      linarith [Pin2.hf_re_nonneg (Lmap hU hσ W A v)]

end Pin2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pin4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

include hU in

theorem pin4 (hPP : PPSemicharSt) (Wu : UnitAt W) (hu : ∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1)
    (hw : A.w0 = H.w0) (a : (W.F.Di (W.ik k)).La) :
    ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a) := by
  rw [hPP Xo c σ r U hU k x W Wu hu a]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (W.F.Di (W.ik k)).EF a (H.w0 • a) := ⟨_, rfl⟩
  rw [← hn]
  have hv := (W.φ k a).2
  have hsm : ((H.w0 : E) • ((W.φ k a : (U.X k).Λ) : Fin r → E)) =
      ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E) := by
    rw [LinearEquiv.map_smul, Submodule.coe_smul]
    rfl
  have he := A.eps_eq _ hv
  rw [hw, hsm, A.im_eq _ hv _ (W.φ k (H.w0 • a)).2] at he
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q = Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm
      ((W.φ k a : (U.X k).Λ) : Fin r → E) ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E)) := ⟨_, rfl⟩
  rw [← hq] at he
  have hi := W.isom k a (H.w0 • a)
  rw [neg_mul, map_neg, ← hq, ← hn] at hi
  have hqr : (q : ℝ) = -(n : ℝ) := by
    have := congrArg (fun t : ℚ => (t : ℝ)) hi
    push_cast at this
    linarith
  have hc : Real.cos (Real.pi * (A.sg * (q : ℝ))) = (-1 : ℝ) ^ n := by
    rw [hqr]
    rcases A.sg_pm with h | h <;> rw [h]
    · rw [show Real.pi * (1 * -(n : ℝ)) = -((n : ℝ) * Real.pi) by ring, Real.cos_neg, Real.cos_int_mul_pi]
    · rw [show Real.pi * (-1 * -(n : ℝ)) = (n : ℝ) * Real.pi by ring, Real.cos_int_mul_pi]
  rw [hc] at he
  have hC := congrArg (fun t : ℝ => (t : ℂ)) he
  push_cast at hC
  exact hC

end Pin4

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Inv

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem e_ne_zero (τ : (U.X k).Ψ) (b : Fin r) : A.e τ b ≠ 0 := by
  intro h0
  have := A.e_orth τ b b
  rw [if_pos rfl, h0] at this
  simp only [hermC, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at this
  unfold sgn at this
  split_ifs at this <;> norm_num at this

theorem yf_ne_zero (hx : (U.X k).IsOrtho x.1) (τ : (U.X k).Ψ) (b : Fin r) : yf A τ b ≠ 0 := by
  intro h0
  have := e_mul A hx (fun τ => (x.2 τ).1) τ b
  change A.e τ b = yf A τ b • col (mat x.1 τ) b at this
  rw [h0, zero_smul] at this
  exact e_ne_zero A τ b this

theorem c_pos (τ : (U.X k).Ψ) : 0 < (U.X k).c τ := by
  unfold Data.c
  have : τ.1 (U.X k).ξ0 ≠ 0 := (map_ne_zero τ.1).mpr (U.X k).ξ0_ne
  have := norm_pos_iff.mpr this
  linarith

theorem wt_ne_zero (hx : (U.X k).IsOrtho x.1) (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) : wt hU A i ≠ 0 := by
  unfold wt
  split_ifs with h
  · refine mul_ne_zero ?_ ?_
    · exact_mod_cast (Real.sqrt_pos.mpr (c_pos _)).ne'
    · rw [map_ne_zero]
      exact yf_ne_zero A hx _ _
  · refine mul_ne_zero ?_ (yf_ne_zero A hx _ _)
    exact_mod_cast (Real.sqrt_pos.mpr (c_pos _)).ne'

include hU hσ in

def Linv : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim →ₗ[ℂ] (Fin W.g → ℂ) where
  toFun v := fun j => v ((letT hU hσ W A).symm j) / wt hU A ((letT hU hσ W A).symm j)
  map_add' v w := by
    funext j
    simp only [PiLp.add_apply, Pi.add_apply, add_div]
  map_smul' a v := by
    funext j
    simp only [PiLp.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, mul_div_assoc]

theorem Linv_Lmap (hx : (U.X k).IsOrtho x.1) (z : Fin W.g → ℂ) : Linv hU hσ W A (Lmap hU hσ W A z) = z := by
  funext j
  show Lmap hU hσ W A z ((letT hU hσ W A).symm j) / wt hU A ((letT hU hσ W A).symm j) = z j
  rw [Lmap_apply, Equiv.apply_symm_apply, mul_div_cancel_left₀ _ (wt_ne_zero hU A hx _)]

theorem Lmap_Linv (hx : (U.X k).IsOrtho x.1) (v : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) :
    Lmap hU hσ W A (Linv hU hσ W A v) = v := by
  ext i
  rw [Lmap_apply]
  show wt hU A i * (v ((letT hU hσ W A).symm (letT hU hσ W A i)) / wt hU A ((letT hU hσ W A).symm (letT hU hσ W A i))) = v i
  rw [Equiv.symm_apply_apply, mul_div_cancel₀ _ (wt_ne_zero hU A hx _)]

end Inv

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi MonObj
open scoped ComplexConjugate CategoryTheory.Obj

theorem differentiable_conj_conj {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => star (f (star z))) := by
  intro x
  have hL : HasFDerivAt f (fderiv ℂ f (star x)) (star x) := (hf (star x)).hasFDerivAt
  set L := fderiv ℂ f (star x) with hLdef
  let D : (Fin n → ℂ) →L[ℂ] ℂ :=
    { toFun := fun v => star (L (star v))
      map_add' := fun v w => by simp only [star_add, map_add]
      map_smul' := fun c v => by
        simp only [star_smul, map_smul, smul_eq_mul, star_mul', star_star, RingHom.id_apply]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  have h1 : HasFDerivAt (fun z : Fin n → ℂ => star z)
      ((starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) x :=
    (starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)).hasFDerivAt
  have h2 : HasFDerivAt f (L.restrictScalars ℝ) (star x) := hL.restrictScalars ℝ
  have h3 : HasFDerivAt (fun w : ℂ => star w) ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) (f (star x)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  have h4 := h3.comp x (h2.comp x h1)
  have hD : ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((L.restrictScalars ℝ).comp
      ((starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))) = D.restrictScalars ℝ :=
    ContinuousLinearMap.ext fun v => rfl
  have h5 : HasFDerivAt (fun z : Fin n → ℂ => star (f (star z))) (D.restrictScalars ℝ) x :=
    h4.congr_fderiv hD
  exact (hasFDerivAt_of_restrictScalars ℝ h5 (rfl : D.restrictScalars ℝ = D.restrictScalars ℝ)).differentiableAt

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)

theorem ex_periodic (a : (W.F.Di (W.ik k)).La) (z : Fin W.g → ℂ) :
    W.F.ex (W.ik k) W.Pm (z + W.Pm a) = W.F.ex (W.ik k) W.Pm z := by
  rw [W.F.ex_add _ _ W.per, (W.F.ex_ker _ _ W.per _).mpr ⟨a, rfl⟩, _root_.mul_one]

theorem primeSpectrum_eq (p q : PrimeSpectrum ℂ) : p = q := by
  first
  | exact Subsingleton.elim p q
  | exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)

theorem exists_chart_pt {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := primeSpectrum_eq q p0
  rw [this]
  exact hj

theorem exists_gx_pt (z : Fin W.g → ℂ) : ∃ pt : Sp ℂ ⟶ Gx (U.un k x).x,
    pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left ∧ pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) := by
  let b : Over.mk (U.un k x).x ⟶ Xo.univ.t.G :=
    Over.homMk (W.F.ex (W.ik k) W.Pm z).left ((Over.w (W.F.ex (W.ik k) W.Pm z)).trans W.pt.symm)
  refine ⟨(CartesianMonoidalCategory.lift (𝟙 (Over.mk (U.un k x).x)) b).left, ?_, ?_⟩
  · exact (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg (fun q => Over.Hom.left q) (CartesianMonoidalCategory.lift_snd _ _))
  · exact (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg (fun q => Over.Hom.left q) (CartesianMonoidalCategory.lift_fst _ _))

theorem theta_add (Wu : UnitAt W) (a : (W.F.Di (W.ik k)).La) (z : Fin W.g → ℂ) :
    Wu.θ (z + W.Pm a) = Wu.χl (W.Pm a) * cexp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
      Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z := by
  obtain ⟨j, hj⟩ := exists_chart_pt Xo.univ.t.PP.L Xo.univ.t.PP.isLB (W.F.ex (W.ik k) W.Pm z).left
  obtain ⟨pt, h1, h2⟩ := exists_gx_pt W z
  have hj' : ⊤ ≤ (W.F.ex (W.ik k) W.Pm (z + W.Pm a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [ex_periodic]
    exact hj
  have e1 := Wu.c7 j z pt h1 h2 hj
  have e2 := Wu.c7 j (z + W.Pm a) pt (by rw [ex_periodic]; exact h1) h2 hj'
  have e3 := (Wu.c6 a j z).2 hj
  have hne := Wu.c3 j (z + W.Pm a) hj'
  have key : Wu.θ (z + W.Pm a) * Wu.fr j (z + W.Pm a) =
      (Wu.χl (W.Pm a) * cexp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
        Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z) * Wu.fr j (z + W.Pm a) := by
    rw [← e2, e1, e3]
    ring
  exact mul_right_cancel₀ hne key

theorem theta_ne (Wu : UnitAt W) : ∃ z, Wu.θ z ≠ 0 := by
  by_contra h
  push Not at h
  have := Wu.c9
  simp [h] at this

end Theta

section Sec

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

def sT (Wu : UnitAt W) : (Fin 1 → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) → ℂ :=
  fun w => star (Wu.θ (star (Linv hU hσ W A (w 0))))

theorem sT_mem (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (hθ : Differentiable ℂ Wu.θ)
    (h4 : ∀ a, ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a)) :
    sT hU hσ W A Wu ∈ A.T.Sec 1 1 := by
  refine ⟨?_, fun gm hgm v => ?_⟩
  · have hL : Differentiable ℂ (fun w : Fin 1 → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim => Linv hU hσ W A (w 0)) :=
      ((LinearMap.toContinuousLinearMap (Linv hU hσ W A)).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) 0)).differentiable
    exact (differentiable_conj_conj hθ).comp hL
  · obtain ⟨v0, hv0, hφ⟩ := (A.lat (gm 0)).mp (hgm 0)
    obtain ⟨a, ha⟩ : ∃ a, ((W.φ k a : (U.X k).Λ) : Fin r → E) = v0 :=
      ⟨(W.φ k).symm ⟨v0, hv0⟩, by simp⟩
    have hgm0 : gm 0 = Lmap hU hσ W A (star (W.Pm a)) := by
      rw [← hφ, ← ha, pin1 hU hσ W A hx a]
    have hLinv : Linv hU hσ W A (gm 0) = star (W.Pm a) := by
      rw [hgm0, Linv_Lmap hU hσ W A hx]
    have hv : v 0 = Lmap hU hσ W A (Linv hU hσ W A (v 0)) := (Lmap_Linv hU hσ W A hx _).symm
    obtain ⟨z, hz⟩ : ∃ z, z = star (Linv hU hσ W A (v 0)) := ⟨_, rfl⟩
    have hHC1 : ReciprocityTheory.ChartRestriction.G.I2.HC v gm = star (hermForm Wu.Hm z (W.Pm a)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.I2.HC, Fin.sum_univ_one]
      rw [hv, hgm0, pin2 hU hσ W A hx Wu, star_star, ← hz]
    have hHC2 : ReciprocityTheory.ChartRestriction.G.I2.HC gm gm = star (hermForm Wu.Hm (W.Pm a) (W.Pm a)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.I2.HC, Fin.sum_univ_one]
      rw [hgm0, pin2 hU hσ W A hx Wu, star_star]
    have heps : ((A.T.eps (gm 0) : ℤ) : ℂ) = Wu.χl (W.Pm a) := by
      rw [← h4 a, ha, hφ]
    have hreal : star (Wu.χl (W.Pm a)) = Wu.χl (W.Pm a) := by
      rw [← heps]
      simp
    show star (Wu.θ (star (Linv hU hσ W A ((v + gm) 0)))) = _ * _ * star (Wu.θ (star (Linv hU hσ W A (v 0))))
    rw [Pi.add_apply, map_add, hLinv, star_add, star_star, ← hz, theta_add W Wu a z, hHC1, hHC2,
      Fin.prod_univ_one, pow_one, heps, star_mul', star_mul', hreal]
    congr 2
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.star_def, Nat.cast_one, _root_.one_mul,
      map_ofNat]
    ring

theorem sT_ne (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) : sT hU hσ W A Wu ≠ 0 := by
  obtain ⟨z, hz⟩ := theta_ne W Wu
  intro h
  have := congrFun h (fun _ => Lmap hU hσ W A (star z))
  simp only [sT, Linv_Lmap hU hσ W A hx, star_star, Pi.zero_apply, star_eq_zero] at this
  exact hz this

def Aθ (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (hθ : Differentiable ℂ Wu.θ)
    (h4 : ∀ a, ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a)) :
    ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1 :=
  { A with s := sT hU hσ W A Wu, s_mem := sT_mem hU hσ W A hx Wu hθ h4, s_ne := sT_ne hU hσ W A hx Wu }


end Sec

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
