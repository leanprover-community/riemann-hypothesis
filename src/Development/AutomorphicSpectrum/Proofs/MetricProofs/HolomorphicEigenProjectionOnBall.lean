module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem perExt_differentiableOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ}
    {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)
    (y : Ψ → Fin (j + j') → ℂ) :
    DifferentiableOn ℂ (fun t => C.perExt (F.R t) y) (ballDom F.q) := by
  have h : (fun t => C.perExt (F.R t) y) =
      fun t => ∑ k, C.bas.equivFun y k • (F.R t).P (C.lam k) := by
    funext t
    exact Module.Basis.constr_apply_fintype ℝ C.bas _ y
  rw [h]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  exact (F.hol.2 (C.lam k)).const_smul (C.bas.equivFun y k)

theorem pPart_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (y : Fin (j + j') → ℂ), DifferentiableOn ℂ (fun t => C.pPart (F.R t) τ y) (ballDom F.q) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ y
  classical
  unfold LatEmb.pPart
  exact ((perExt_differentiableOn C _).sub
    ((perExt_differentiableOn C _).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
