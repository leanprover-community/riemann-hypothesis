module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix

open Formalism.BasicNotions Formalism.MainNotions.N

noncomputable def thetaGram {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    what₂.Mj j →ₗ[ℂ] what₂.Mj j :=
  what₂.thetaP μ j ∘ₗ what₂.thetaT μ j

def ThetaGramPositiveScalar {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (_A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT),
    (∀ f ∈ what₂.isot (N.j i) σ,
      thetaGram what₂ (N.mu i) (N.j i) f = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) • f) ∧
    (what₂.isot (N.j i) σ ≠ ⊥ → 0 < what₂.lamP (N.mu i) (N.j i) σ)

theorem ThetaGramPositiveScalar.norm_sq {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ) :
    ‖what₂.thetaT (N.mu i) (N.j i) f‖ ^ 2 = what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 := by
  have hg := (h i σ).1 f hf
  simp only [thetaGram, LinearMap.comp_apply] at hg
  have key : inner ℂ (what₂.thetaT (N.mu i) (N.j i) f) (what₂.thetaT (N.mu i) (N.j i) f)
      = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) * inner ℂ f f := by
    show inner ℂ (LinearMap.adjoint (what₂.thetaP (N.mu i) (N.j i)) f)
      (what₂.thetaT (N.mu i) (N.j i) f) = _
    rw [LinearMap.adjoint_inner_left, hg, inner_smul_right]
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  simp

theorem ThetaGramPositiveScalar.eq_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ)
    (h0 : what₂.thetaT (N.mu i) (N.j i) f = 0) : f = 0 := by
  by_contra hne
  have hpos : 0 < what₂.lamP (N.mu i) (N.j i) σ := by
    apply (h i σ).2
    intro hb
    rw [hb] at hf
    exact hne ((Submodule.mem_bot ℂ).1 hf)
  have e := h.norm_sq i σ f hf
  rw [h0, norm_zero] at e
  have e2 : what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 = 0 := by rw [← e]; norm_num
  rcases mul_eq_zero.1 e2 with h1 | h1
  · exact absurd h1 hpos.ne'
  · exact hne (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix
