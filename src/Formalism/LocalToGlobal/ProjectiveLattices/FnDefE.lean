module

import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableIndicatorOfContOn
public import Formalism.LocalToGlobal.ProjectiveLattices.NrmTieDef
public import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  have hconj : ∀ z : E, τ.1 (cc z) = starRingEnd ℂ (τ.1 z) := fun z =>
    NumberField.IsCMField.complexEmbedding_complexConj E τ.1 z
  have hcc : ∀ (b q : Fin r), cc ((Pi.single b (1 : E) : Fin r → E) q) =
      (Pi.single b (1 : E) : Fin r → E) q := by
    intro b q
    by_cases h : q = b
    · subst h
      simp [cc]
    · simp [cc, Pi.single_eq_of_ne h]
  have hU : ∀ a b : Fin r, ∑ p, ∑ q, (γ : Matrix (Fin r) (Fin r) E) p a * X.Gm p q *
      cc ((γ : Matrix (Fin r) (Fin r) E) q b) = X.Gm a b := by
    intro a b
    have h := (X.Γ_stab γ hγ).1 (Pi.single a 1) (Pi.single b 1)
    simp only [herm, hcc] at h
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hUm : Matrix.transpose (γ : Matrix (Fin r) (Fin r) E) * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
    ext a b
    rw [← hU a b]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hg : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      gram τ.1 X.Gm M = Matrix.transpose M * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    intro M
    ext a b
    simp only [gram, Matrix.of_apply, hermC, col, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hmat : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    ext a b
    simp only [Matrix.map_apply, hconj]
  have e : X.Gm.map τ.1 = (Matrix.transpose (γ : Matrix (Fin r) (Fin r) E)).map τ.1 * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    conv_lhs => rw [← hUm]
    rw [Matrix.map_mul, Matrix.map_mul]
  have key : gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    rw [hg, hg, hmat, Matrix.transpose_mul, Matrix.map_mul, hc, ← Matrix.transpose_map]
    conv_rhs => rw [e]
    simp only [Matrix.mul_assoc]
  unfold dmin
  rw [key]

theorem dmin_ne_of_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h0
  have h1 : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
    first
      | exact (hx τ).2 i
      | (simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
         exact (hx τ).2 i)
  rw [h0] at h1
  simp at h1

theorem continuousOn_pnorm (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom) :
    ContinuousOn (X.pnorm la P) X.dom := by
  apply GlobalTheory.KronOff.pnorm_contOn <;> assumption

end FD


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


section Core

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps CompSplitPfB

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)


variable {j} in
def CompOf (cm : ∀ σ : Tc.Q.c.F →+* ℂ, (Tc.U j σ).Comp → Comp (Tc.Q.Xo j) Tc.Q.c) : Prop :=
  ∀ (σ : Tc.Q.c.F →+* ℂ) (k : (Tc.U j σ).Comp) (x : ((Tc.U j σ).X k).dom) (q : PrimeSpectrum (CAt σ)),
    cspB_lift ((Tc.U j σ).un k x).x ((Tc.U j σ).un k x).x_over q ∈
      ((cm σ k : Comp (Tc.Q.Xo j) Tc.Q.c) : Set ((Tc.Q.Xo j).XF Tc.Q.c))

def ptAt (hj : InR D j) (hA : AllTest (Tc.Q.Xo j) Tc.Q.c) (hB : ∀ σ, GoodEmb Tc.Q.c σ → BCEx (Tc.Q.Xo j) Tc.Q.c σ)
    (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c) (hb : CBaseEx (Tc.Q.Xo j) Tc.Q.c h) (Z : Comp (Tc.Q.Xo j) Tc.Q.c)
    (P : Om Z →+* ℂ) (sg : Tc.Q.c.F →+* ℂ) (hP : sgOf P = sg) : SupPtAt j (goodOf Tc.Q.c sg) :=
  hP ▸ nrmTieDefPt hL j hj hA hB h hb Z P

end Core

end Formalism.L2.Pj
