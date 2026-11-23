module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SquareIntegrableGeneratedVectors

@[expose] public section

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem pm_induction {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ) {lam : Fin n → ℝ}
    (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hm : thrStar ε + m < h)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ idx : Fin m → Fin n × Fin n,
        ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
            ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
          C * NE (smE ε (rreg ε)) (m * (n - 1)) x * NE (smE ε (rreg ε)) (m * (n - 1)) y :=
  pmProp_of_gap hp hq m hlam hgap hm T Ψ v₀ hP hv₀

end ReciprocityTheory.ChartRestriction.DS.DecInf
