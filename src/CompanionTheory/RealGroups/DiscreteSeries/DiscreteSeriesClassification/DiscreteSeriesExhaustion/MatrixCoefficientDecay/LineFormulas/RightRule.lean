module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgExh.Dec.N

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

def OdeA : Prop :=
  ∀ (z : ℂ) (s : ℝ), z.re < s → ∀ f g : ℝ → ℂ, (∀ t, 0 ≤ t → HasDerivAt f (z * f t + g t) t) → Continuous g →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖g t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤ →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤

def OdeB : Prop :=
  ∀ (z : ℂ) (s s' : ℝ), s < z.re → s' ≤ z.re → ∀ f g : ℝ → ℂ, (∀ t, 0 ≤ t → HasDerivAt f (z * f t + g t) t) →
    Continuous g →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖g t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤ →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s' * t))) < ⊤ →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤

def RightRule : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V) (X : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε X →
      ∀ g, Formalism.REAL.inUJ ε g →
        HasDerivAt (fun t : ℝ => (famP σ D E hK.gl χ ss i u) (g * NormedSpace.exp ((t : ℂ) • X)))
          ((famP σ D E hK.gl χ ss i (∑ a, ∑ b, X a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b u)) g) 0

def LeftRule : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ i : D × List (Fin n), ∃ l : Fin n → Fin n → (D × List (Fin n)) →₀ ℂ,
      ∀ (a b : Fin n) (u : (path ⟨D, E, hK.gl⟩ χ ss).V) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
        (famP σ D E hK.gl χ ss i ((path ⟨D, E, hK.gl⟩ χ ss).E a b u)) g =
          ∑ c, ∑ d, (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c d *
            (l c d).sum fun i' r => r * (famP σ D E hK.gl χ ss i' u) g

end CompanionTheory.RgExh.Dec.N
