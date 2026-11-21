import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
import Formalism.LocalToGlobal.ProjectiveLattices.OpenRowsFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramePointCombinationMatrix

section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram.Comb

theorem sum_shift {r p m : ℕ} (hm : p + m = r) (f : Fin r → ℂ) (h : ∀ c : Fin r, (c : ℕ) < p → f c = 0) :
    ∑ c, f c = ∑ i : Fin m, f ⟨p + i, by omega⟩ := by
  subst hm
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (fun c _ => h _ (by simp)), zero_add]
  rfl

theorem sum_rev {r p : ℕ} (hp : p ≤ r) (f : Fin r → ℂ) (h : ∀ c : Fin r, p ≤ (c : ℕ) → f c = 0) :
    ∑ c, f c = ∑ i : Fin p, f ⟨p - 1 - i, by omega⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (s := Finset.univ) (f := fun i : Fin m => f (Fin.natAdd p i))
    (fun c _ => h _ (by simp)), add_zero, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  apply Fin.ext
  simp [Fin.val_rev]
  omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_comb (X : Data E r) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (ρ : E →+* ℂ) (m : ℕ) (hm : ρ ∈ X.Ψ → m = r - X.p0) (hm' : ρ ∉ X.Ψ → m = X.p0)
    (v : Fin r → E) (b : ℕ) (hb : b < m) :
    Formalism.L2.PjFree.perFr X x' v ρ b = ∑ i : Fin m, coef X x x' ρ b i * Formalism.L2.PjFree.perFr X x v ρ i := by
  have hp := X.p0_le
  by_cases h : ρ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨ρ, h⟩).det := (hx _).1.isUnit
    have hb' : X.p0 + b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) ⟨_, hb'⟩ c *
        ((mat x ⟨ρ, h⟩)⁻¹.mulVec (Data.emb ρ v)) c := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨ρ, h⟩) (mat x' ⟨ρ, h⟩)⁻¹ hd, ← mulVec_mulVec]
      rfl
    rw [e1, sum_shift (p := X.p0) (m := m) (by omega) _
      (fun c hc => by rw [h2 _ _ _ (Nat.le_add_right _ _) hc, zero_mul])]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 + (i : ℕ) < r := by have := i.2; omega
    congr 1
    · simp only [coef, dif_pos h, ent]
      rw [dif_pos (And.intro hb' hi)]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hi]
  · obtain rfl := hm' h
    have h' : conjEmb ρ ∈ X.Ψ := by_contra fun h' => h ((X.cmType ρ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hb' : X.p0 - 1 - b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) c ⟨_, hb'⟩ *
        hermC (conjEmb ρ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) c) (Data.emb (conjEmb ρ) v) := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
      generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
      simp only [hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
    rw [e1]
    refine Eq.trans (sum_rev hp _ fun c hc => ?_) ?_
    · rw [h1 _ _ _ hc (by simp only; omega), zero_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 - 1 - (i : ℕ) < r := by omega
    have hi2 : (i : ℕ) < X.p0 := by have := i.2; omega
    congr 1
    · simp only [coef, dif_neg h, dif_pos h', ent]
      rw [dif_pos (And.intro hi hb')]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hi]

def hmap {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) :
    (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z := fun j => ∑ i : Fin (μ (e j).1), C (e j).1 (e j).2 i * z (e.symm ⟨(e j).1, i⟩)
  map_add' z w := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    funext j
    simp [Finset.mul_sum, mul_left_comm]

theorem hmap_apply {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (z : Fin g → ℂ)
    (τ : T) (b : Fin (μ τ)) : hmap e C z (e.symm ⟨τ, b⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
  have key : ∀ s : Σ τ : T, Fin (μ τ), s = ⟨τ, b⟩ →
      ∑ i : Fin (μ s.1), C s.1 s.2 i * z (e.symm ⟨s.1, i⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
    rintro _ rfl
    rfl
  exact key _ (e.apply_symm_apply _)

theorem hmap_single {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (τ : T)
    (i : Fin (μ τ)) : hmap e C (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ b : Fin (μ τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) := by
  funext j
  obtain ⟨⟨τ', b'⟩, rfl⟩ := e.symm.surjective j
  rw [hmap_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    have hs : ∀ a b : Fin (μ τ'), (Pi.single (e.symm ⟨τ', a⟩) (1 : ℂ) : Fin g → ℂ) (e.symm ⟨τ', b⟩) =
        if a = b then 1 else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simp
      · rw [if_neg hab, Pi.single_eq_of_ne (fun h => hab (by simpa using h.symm))]
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e' (h z) = e z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e w v) : IsDerivAt0 e' (h w) v := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [hd.1, ← he 0, map_zero]
  · rw [hd.2 U hU f]
    let hc : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := h.toContinuousLinearEquiv
    have e1 : (fun z => valAt' (e z) U f) = (fun z => valAt' (e' z) U f) ∘ hc := by
      funext z
      simp only [Function.comp, hc, LinearEquiv.coe_toContinuousLinearEquiv', he]
    rw [e1, hc.comp_right_fderiv]
    simp [hc]

end GlobalTheory.FramePairGram.Comb

open GlobalTheory.FramePairGram.Comb in

theorem GlobalTheory.FramePairGram.lie_comb_of_block : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.GoodEmb c σ → ∀ (k : U.Comp) (x x' : (U.X k).dom), (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0) → (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), Formalism.L2.Pj.IsCombAt (U.un k x').x ((U.un k x').u τ) (fun b => (coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i : CAt σ)) ((U.un k x).u τ i) := by
  intro E _ _ _ r H Dw l Xo c σ U hU hσ k x x' h1 h2 τ i
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, hu, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', hu', -⟩ := hF k x'
  obtain ⟨hEU, hEL, -, -⟩ := GlobalTheory.exp_four_clauses E H Dw l Xo c σ hσ g e F
  let C : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ b i => coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i
  have hL : ∀ a, P' a = hmap e C (P a) := fun a => funext fun j => by
    rw [hP', perFr_comb (U.X k) x.2 h1 h2 _ (Dw.mult (e j).1)
      (fun h => (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega))
      (fun h => (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm) _ _ (e j).2.2]
    simp only [hmap, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP, Equiv.apply_symm_apply]
  have hsurj : Function.Surjective (hmap e C) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (hmap e C)).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  let hE : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (hmap e C) ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  have hex : ∀ z, (F.ex (ik k) P' (hE z)).left = (F.ex (ik k) P z).left :=
    hEU (ik k) P P' hper hper' (LinearEquiv.refl _ _) hE (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
      (fun a => ⟨0, by simp⟩) hL
  have hd := isDerivAt0_comp (fun z => (F.ex (ik k) P z).left) (fun z => (F.ex (ik k) P' z).left) hE hex (hu τ i)
  have hs : hE (Pi.single (e.symm ⟨τ, i⟩) 1) = ∑ b : Fin (Dw.mult τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) :=
    hmap_single e C τ i
  rw [hs] at hd
  rw [hx']
  exact hEL (ik k) P' hper' _ (fun b => Pi.single (e.symm ⟨τ, b⟩) 1) ((U.un k x').u τ) _ _ (fun b => hu' τ b) hd

end
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram

theorem coef_eq_coW_change {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin j => coef X x x' τ.1 b i) = (coW X hj x' τ)⁻¹ * coW X hj x τ := by
  have hd' : IsUnit (mat x' τ).det := (hx' τ).1.isUnit
  have hN : frameCo X hj x τ = frameCo X hj x' τ * reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) := by
    simp only [frameCo, reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd']
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hW : coW X hj x τ = coW X hj x' τ * (reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ)).toBlocks₁₁ := by
    unfold coW
    rw [h, hN, moeb_zero]
    generalize frameCo X hj x' τ = g at *
    generalize reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) = N
    have e11 : (g * N).toBlocks₁₁ = g.toBlocks₁₁ * N.toBlocks₁₁ + g.toBlocks₁₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]
    have e21 : (g * N).toBlocks₂₁ = g.toBlocks₂₁ * N.toBlocks₁₁ + g.toBlocks₂₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    rw [e11, e21]
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu']
    abel
  rw [hW, ← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 ((isUnit_iff_isUnit_det _).2 (isUnit_coW X hj hp hx' τ))), Matrix.one_mul]
  ext b i
  have hb : X.p0 + (b : ℕ) < r := by have := b.2; have := X.p0_le; omega
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; have := X.p0_le; omega
  have eb : (idx hj).symm (Sum.inl b) = ⟨X.p0 + b, hb⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (b : ℕ) = X.p0 + b; omega)
  have ei : (idx hj).symm (Sum.inl i) = ⟨X.p0 + i, hi⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (i : ℕ) = X.p0 + i; omega)
  simp only [of_apply, coef, dif_pos τ.2, ent, dif_pos (And.intro hb hi), Subtype.coe_eta, toBlocks₁₁, reindex_apply,
    submatrix_apply, eb, ei]

end GlobalTheory.FramePairGram
end
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePairGram

theorem coef_conj_eq_coOm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin (r - j) => coef X x x' (conjEmb τ.1) b i) =
      (((coOm X hj x τ)⁻¹ * coOm X hj x' τ)ᵀ).submatrix Fin.rev Fin.rev := by
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ =
      reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have h12 : (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₁₂ = 0 := by
    ext a c
    simp only [toBlocks₁₂, of_apply, reindex_apply, submatrix_apply, Matrix.zero_apply]
    apply PointWell.block_of_moeb_eq X hj hp hx hx' τ h
    · rw [idx_symm_inl, hp]; omega
    · rw [idx_symm_inr, hp]; exact c.2
  have hO : (coOm X hj x τ)⁻¹ * coOm X hj x' τ =
      (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
    have e : frameCo X hj x' τ = frameCo X hj x τ * reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
      rw [← hN, mul_nonsing_inv_cancel_left _ _ hf]
    have e2 : coOm X hj x' τ = coOm X hj x τ * (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
      rw [coOm, coOm, e]
      conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj x τ),
        ← fromBlocks_toBlocks (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)), fromBlocks_multiply,
        toBlocks_fromBlocks₂₂]
      rw [h12, Matrix.mul_zero, zero_add]
    rw [e2, ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_coOm X hj hp hx τ), Matrix.one_mul]
  have cc : conjEmb (conjEmb τ.1) = τ.1 := RingHom.ext fun a => by simp [conjEmb]
  have hcc : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [cc]; exact τ.2
  have hc : conjEmb τ.1 ∉ X.Ψ := fun hc => ((X.cmType τ.1).mp τ.2) hc
  have hs : (⟨conjEmb (conjEmb τ.1), hcc⟩ : X.Ψ) = τ := Subtype.ext cc
  rw [hO]
  ext b i
  have hb := b.2
  have hi := i.2
  have hl : X.p0 - 1 - (i : ℕ) < r ∧ X.p0 - 1 - (b : ℕ) < r := by omega
  simp only [of_apply, submatrix_apply, transpose_apply, coef, dif_neg hc, dif_pos hcc, ent, dif_pos hl, hs,
    toBlocks₂₂, reindex_apply]
  refine congrArg₂ _ (Fin.ext ?_) (Fin.ext ?_) <;> simp [idx_symm_inr, Fin.val_rev, hp] <;> omega

end GlobalTheory.FramePairGram
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier
  GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.HodgeOnDomain

attribute [local instance] Over.cartesianMonoidalCategory

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem eigGram_transport {σ : c.F →+* ℂ} (M : EigMet Z σ) {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    M.gram p F τ = Tᴴ * M.gram q G τ * T := by
  subst e
  rw [M.change p G F τ, EigFrame.co_eq h]

theorem eigGram_of_comb {σ : c.F →+* ℂ} (M : EigMet Z σ) (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x)
    (τ : E →+* ℂ) (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    M.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * M.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine eigGram_transport M (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

theorem eq_of_conj_eq_one {n : Type} [Fintype n] [DecidableEq n] {W P : Matrix n n ℂ} (hW : IsUnit W.det)
    (h : Wᴴ * P * W = 1) : P = (W⁻¹)ᴴ * W⁻¹ := by
  have hW' : IsUnit Wᴴ.det := by rw [det_conjTranspose]; exact hW.star
  calc P = (Wᴴ)⁻¹ * (Wᴴ * P * W) * W⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hW, ← Matrix.mul_assoc, nonsing_inv_mul _ hW',
          Matrix.one_mul]
    _ = (W⁻¹)ᴴ * W⁻¹ := by rw [h, Matrix.mul_one, conjTranspose_nonsing_inv]

theorem smul_submatrix_sq {m n : Type} (a : ℂ) (M : Matrix n n ℂ) (e : m → n) :
    (a • M).submatrix e e = a • M.submatrix e e := rfl

end GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeOnDomain

end GlobalTheory.HodgeOnDomain
end
end
