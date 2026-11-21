import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst

noncomputable section

namespace GlobalTheory.FrameUnif.Tests

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem perFr_add (X : Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ τ : E →+* ℂ, Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := fun τ => by
    funext a; simp [Data.emb]
  unfold perFr
  split_ifs
  · rw [he, Matrix.mulVec_add]; rfl
  · simp
  · rw [he]; simp [hermC, mul_add, Finset.sum_add_distrib]
  · simp
  · simp


theorem normConst_pos {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) : 0 < normConst ty ξ₀ := by
  unfold normConst
  refine Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))
  have : ty j ξ₀ ≠ 0 := (map_ne_zero _).2 h
  positivity




open Classical in

theorem models_of_latModel {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (Gm : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (Gm a b) = Gm b a) (hdet : Gm.det ≠ 0)
    (hrk : r = Dw.p + Dw.q)
    (hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (ξ₀ : E) (hξ : cc ξ₀ = -ξ₀) (hξ0 : ξ₀ ≠ 0) (hneg : ∀ τ ∈ Ψ, (τ ξ₀).im < 0)
    (hL : ∀ i, LatModel l Ψ Gm ξ₀ Dw.q (F.Di i)) :
    ∃ M : ModelsOf F r, ModelBase M ∧ NegXi M := by
  choose φ0 h1 h2 h3 h4 h5 h6 h7 using hL
  choose den hd1 hd2 using h4
  choose m hm1 hm2 using h7
  let X : Fin F.n → Data E r := fun i =>
    { Ψ := Ψ, cmType := hcm, Gm := Gm, Gm_herm := hG, Gm_det := hdet, p0 := Dw.q, p0_le := by omega
      signature := hsig
      Λ := LinearMap.range (φ0 i)
      Λ_fg := by
        have := (F.Di i).fin
        rw [LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      Λ_span := h3 i, den := den i, den_ne := hd1 i, Λ_int := hd2 i
      Γ := princ l Gm (F.Di i) (φ0 i)
      Γ_stab := fun _ hγ => hγ.1
      Γ_index := h5 i, Γ_free := h6 i
      χ := fun _ _ => 1
      χ_mul := fun _ _ _ _ _ => (mul_one 1).symm
      χ_add := fun _ _ _ _ => (mul_one 1).symm
      χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩
      ξ0 := ξ₀, ξ0_im := hξ, ξ0_ne := hξ0, κ0 := 2 * ξ₀, κ0_xi := Or.inl rfl
      κ0_sign := fun τ => by
        have := hneg τ.1 τ.2
        rw [map_mul, map_ofNat]
        simp
        linarith
      m := m i, m_pos := hm1 i
      transv := fun ξ hξ' h0 s hs hsi => hm2 i _ (Or.inl rfl) ξ hξ' h0 s hs hsi }
  refine ⟨⟨X, fun i => LinearEquiv.ofInjective (φ0 i) (h1 i)⟩, ?_, fun _ τ hτ => hneg τ hτ⟩
  exact
    { rank := hrk
      type := fun k => ⟨rfl, hΨ⟩
      chi := fun _ _ _ => rfl
      ef := fun k a b => h2 k a b
      gam := fun k γ => Iff.rfl
      domStab := fun k _ hx => ⟨fun _ hb => dom_rmul (X k) hx hb, fun _ hγ => dom_lact (X k) hx hγ.1⟩ }


end GlobalTheory.FrameUnif.Tests
