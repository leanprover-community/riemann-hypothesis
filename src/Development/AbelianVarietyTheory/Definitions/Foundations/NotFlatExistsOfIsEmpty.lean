import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

noncomputable section

namespace GlobalTheory.FlatLine.Model

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_vAdd_two_ne (K : Type) [Field K] [NumberField K] :
    ∃ w : HeightOneSpectrum (𝓞 K), vAdd w (2 : K) ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := sum_vAdd_nat (K := K) (n := 2) two_ne_zero
  simp only [Nat.cast_ofNat, h, Int.cast_zero, zero_mul, finsum_zero] at h1
  exact (Real.log_pos one_lt_two).ne h1

theorem exists_constSec (h1 : N1c) (h2 : GlobalTheory.Published.HasseNormSt) (Xo : Moduli Dw l) (c : Coeff l)
    (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (x : ℝ) :
    ∃ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q), (∀ σ, GoodEmb c σ → IsUnf (U σ)) ∧ Nonempty (Comp Xo c) ∧
      ∀ Z : Comp Xo c, ∃ s : ConstSec U x Z 0 0, (∀ σ, s.cInf σ = 2) ∧ (∃ w, s.rho_vw w ≠ 0) ∧ s.deg = 0 := by
  classical
  have hex : ∀ σ : c.F →+* ℂ, ∃ U : Unf Xo c σ (Dw.p + Dw.q), GoodEmb c σ → IsUnf U := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hU⟩ := GlobalTheory.IsUnfEx.exists_isUnf h1 h2 GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
        GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ hpq hσ
      exact ⟨⟨U.Comp, U.X, U.un⟩, fun _ => hU⟩
    · exact ⟨⟨Empty, fun k => k.elim, fun k => k.elim⟩, fun h => absurd h hσ⟩
  choose U hU using hex
  refine ⟨U, hU, (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l Xo c hpq).1, fun Z => ?_⟩
  have h := hasPts U hpq hg hU Z
  obtain ⟨w, hw⟩ := exists_vAdd_two_ne c.F
  refine ⟨(ConstSec.one x h).smul 2 two_ne_zero, fun σ => ?_, ⟨w, ?_⟩,
    (ConstSec.deg_smul _ _ _).trans (ConstSec.deg_one h)⟩
  · show ‖σ 2‖ * 1 = 2
    rw [map_ofNat]; simp
  · show (vAdd w (2 : c.F) : ℝ) + 0 ≠ 0
    simpa using hw

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}






def twoFr (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r := fun _ => ((2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) :)




def rescale {Z : Comp Xo c} {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) (x' : ℝ) :
    ConstSec U x' Z la δ :=
  { s with
    cInf := (fun _ => lieFacZ Dw x' (wtOf Dw la 0) / lieFacZ Dw x (wtOf Dw la 0)) * s.cInf
    cInf_pos := fun σ => mul_pos (div_pos (lieFacZ_pos _ _) (lieFacZ_pos _ _)) (s.cInf_pos σ)
    norm_inf := fun σ => image_eq_singleton_iff.2 ⟨(s.hasPts.1 σ).1, fun z hz => by
      have := (lieFacZ_pos (Dw := Dw) x (wtOf Dw la 0)).ne'
      rw [Pi.mul_apply, ← s.homN_eq hz, homN, homN]; field_simp⟩ }

theorem sum_flatWt (τ : Psi H) :
    ∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) = Dw.q - Dw.p := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := by simp [Datum.mult, h]
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 :=
        fun i => by
          have := wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)
          rw [this]
          simp [flatWt, parWt, Subtype.ext_iff]
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := by simp [Datum.mult, h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, Subtype.ext_iff, e, conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp [key]




end GlobalTheory.FlatLine.Model
