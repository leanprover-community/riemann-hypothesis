module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.GamDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gamDisc : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ U ∈ 𝓝 (1 : H), ∀ g : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → g ∈ U → g = 1) := by
  intro r X H _
  have hS := GlobalTheory.LatFin.latFin.2 r X 2
  set S := {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
    ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef
  let F : GL (Fin r) E → Set H := fun γ => {g : H | ∀ τ : X.Ψ,
    ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  have hF : ∀ γ, (F γ).Finite := by
    intro γ
    refine Set.Subsingleton.finite ?_
    intro g hg g' hg'
    refine Subtype.ext (funext fun τ => Units.ext ?_)
    exact (hg τ).trans (hg' τ).symm
  have hT : (⋃ γ ∈ S, F γ).Finite := hS.biUnion fun γ _ => hF γ
  have hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H) :=
    (hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r),
      ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2 := by
    simp only [Filter.eventually_all]
    intro τ a b
    have hc : Continuous fun g : H =>
        ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ :=
      ((Units.continuous_val.comp
        ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨_, Filter.inter_mem hC hV, ?_⟩
  rintro g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩
  by_contra hne
  refine h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩
  have := h2 τ a b
  rw [hg τ] at this
  exact this.le

end GlobalTheory.GamDisc
