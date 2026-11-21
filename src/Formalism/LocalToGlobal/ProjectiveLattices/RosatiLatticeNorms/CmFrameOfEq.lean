import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkNum
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound

noncomputable section

namespace Formalism.L2.Pj.abelian₂

open CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {D : D7}

theorem cm_frame_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (Y : Data E r)
    (hX : Xx.toData = Y) (la : Wt Y.Ψ r) (P : Frame Y.Ψ r → ℂ) (z0 : Frame Y.Ψ r) (M w : ℝ)
    (hSS : P ∈ Y.SS la) (hM : 0 < M) (hw : (∑ τ, Y.spread la τ) ≤ w) (hw1 : 1 ≤ w) (hr : 0 < r)
    (htr : ∀ v ∈ Xx.L', herm Y.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Y.Γ, Y.χ la γ = 1 ∧
        ∀ τ : Y.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Y.flowMat v τ ((M : ℂ) * τ.1 b))
    (hz0 : z0 ∈ Y.dom) (hhalf : ∀ x ∈ Y.dom, Y.pnorm la P x ≤ 2 * Y.pnorm la P z0)
    (hpos : 0 < Y.pnorm la P z0) :
    ∃ (x : Frame Y.Ψ r) (lam : Fin r → Fin r → E), x ∈ Y.dom ∧
      LamBasis Xx (frameBasisRadius r Xx.p0 (fdeg E) (dE E) (Real.sqrt (epStar M (fdeg E) w Xx.k0))
        (3 * frameRadius w r / 5)) (hX ▸ x) lam ∧
      P x ≠ 0 := by
  subst hX
  obtain ⟨x, lam, hx, hL, hP, -⟩ := cm_frame Xx la P z0 M w hSS hM hw hw1 hr htr hz0 hhalf hpos
  exact ⟨x, lam, hx, hL, hP⟩

open Classical in

def LamTieSt (T : Formalism.L2.Pj.Core D) (h : LawsCore T) (j : ℕ) (w : WeightFamilies.Wt D j) (La : ℝ) (aMax : ℕ) : Prop :=
  letI := T.Q.H.starRing
  ∀ (k : (T.U j T.σ₀).Comp) (x₀ : ((T.U j T.σ₀).X k).dom) (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q)
    (L : LamLetters o) (σ₁ : o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀) (y : FrPt (T.Q.Xo j) T.Q.c o.K₁)
    (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)), LamPtClauses T j La k x₀ o L σ₁ y eY →
    ∀ F : (recB h).Cusp j w, F ∈ (recB h).Mlat j w → F ≠ 0 → rdU (T.U j T.σ₀) F.1 k x₀.1 ≠ 0 →
    ∃ (a : ∀ b, Fin (L.m b) → ℕ) (G : MvPolynomial (FrVar L.m) o.K₁), G ≠ 0 ∧ (∑ b, ∑ i, a b i) ≤ aMax ∧
      (∀ p, Step5Loc L.e o.Tl.dual o.LamL L.ℓ L.U G w.n p) ∧
      ∀ σ : o.K₁ →+* ℂ, Step5Arch L.e o.Tl.dual o.LamL L.ℓ L.U G a w.n La
        ((recB h).supN j w (σ.comp (algebraMap T.Q.c.F o.K₁)) F) σ

theorem LamLetters.lines {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
    {c : Coeff l} {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La logOm : ℝ} (hG : LamObjGood o f La) (L : LamLetters o)
    (hL : L.IsGood) (hdeg : (∀ k, (o.ℓΨ k).ndeg = logOm / 2) ∧ ∀ k, (o.ℓ' k).ndeg = logOm / 2) :
    (∀ k, (L.ℓ k).Good) ∧ ∀ k, (L.ℓ k).ndeg = logOm / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hΨ, h', -⟩ := hG
  have key : ∀ k, (L.ℓ k).Good ∧ (L.ℓ k).ndeg = logOm / 2 := by
    intro k
    have h := hL.2.2.2 k
    rcases hs : L.src k with q | q
    · simp only [hs] at h
      rw [h]
      exact ⟨(hΨ q.2).1, hdeg.1 q.2⟩
    · simp only [hs] at h
      rw [h]
      exact ⟨(h' q.2).1, hdeg.2 q.2⟩
  exact ⟨fun k => (key k).1, fun k => (key k).2⟩

def laOf {T : Formalism.L2.Pj.Core D} {j : ℕ} (Xx : (T.U j T.σ₀).Comp → DataX D.host.E D.R.r) (M wf : ℝ)
    (k : (T.U j T.σ₀).Comp) : ℝ :=
  frameBasisRadius D.R.r (Xx k).p0 (fdeg D.host.E) (dE D.host.E) (Real.sqrt (epStar M (fdeg D.host.E) wf (Xx k).k0))
    (3 * frameRadius wf D.R.r / 5)


end Formalism.L2.Pj.abelian₂
