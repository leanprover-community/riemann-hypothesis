module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.LowWeightDensity
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem signs {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}
    {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) : (∃ a, ε' a = false) ∧ (∃ a, ε' a = true) := by apply LowWeightDensity.signs <;> assumption

theorem exists_ds {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) (hm : 1 ≤ m) (hc : Formalism.QuantumDeterminants.IsHCParam lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ := by apply LowWeightDensity.exists_ds <;> assumption

theorem dense_sm {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S} (hm : 2 ≤ m)
    (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDS ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3))
    (hS : IsSmMod ε σ S E) : Dense (S : Set H) := by apply LowWeightDensity.dense_sm <;> assumption

theorem exists_low {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ w ∈ lowKSub ε lam σ, ‖w‖ = 1 := by apply LowWeightDensity.exists_low <;> assumption

theorem exists_P {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} {lam : Fin (n + 1) → ℝ}
    {mu : Fin n → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hF : Fits ε ε' e) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ)
    {j : H' →L[ℂ] H} (hj : j ≠ 0) (hjm : IsHMap ε' e π σ j) : ∃ P : H →L[ℂ] H', Intertw ε' e π σ P ∧ P ≠ 0 := by apply LowWeightDensity.exists_P <;> assumption

theorem decay_low {n : ℕ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)} (hn : 1 ≤ n) (hc : Formalism.QuantumDeterminants.IsHCParam mu) (hσ : IsDS ε' mu σ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)) {w : K} (hw : w ∈ lowKSub ε' mu σ) (hw1 : ‖w‖ = 1) :
    Continuous (fun h : UJ ε' => conj ⟪w, σ (um h) w⟫_ℂ) ∧ ∃ C : ℝ, ∀ h : UJ ε',
      ‖conj ⟪w, σ (um h) w⟫_ℂ‖ ≤ C * hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + (n : ℝ))) := by apply LowWeightDensity.decay_low <;> assumption

end PositivityTheory.RgHe.SM
