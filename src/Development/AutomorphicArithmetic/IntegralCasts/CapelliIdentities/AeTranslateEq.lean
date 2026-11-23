module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

theorem UpperTheory.ae_translate_eq :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace X]
        (μ : MeasureTheory.Measure G) [μ.IsMulRightInvariant] (ν : MeasureTheory.Measure X) (q : G → X) (ρ : X → X) (g : G)
        (v v' : X → ℂ) (φ : G → ℂ), MeasureTheory.Measure.QuasiMeasurePreserving q μ ν → (∀ y, ρ (q y) = q (y * g)) →
        (v' =ᵐ[ν] fun x => v (ρ x)) → (∀ᵐ y ∂μ, v (q y) = φ y) → ∀ᵐ y ∂μ, v' (q y) = φ (y * g) := by
  intro G X _ _ _ _ μ _ ν q ρ g v v' φ hq hρ hv hφ
  have h1 : ∀ᵐ y ∂μ, v' (q y) = v (ρ (q y)) := MeasureTheory.Measure.QuasiMeasurePreserving.ae hq hv
  have h2 : ∀ᵐ y ∂μ, v (q (y * g)) = φ (y * g) :=
    (MeasureTheory.measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hφ
  filter_upwards [h1, h2] with y a b
  rw [a, hρ, b]
