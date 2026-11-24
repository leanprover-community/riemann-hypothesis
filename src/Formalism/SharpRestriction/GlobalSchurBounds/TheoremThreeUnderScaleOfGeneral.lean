module

public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

def DiscreteSeriesDegreeBoundsOfScaleAgreement (D : D7) : Prop := cdScaleTie D → StandardLattice.DiscreteSeriesDegreeBoundsOfGap D

def cdScaleTieR (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((s n ε : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

theorem cdScaleTie_iff (D : D7) : cdScaleTie D ↔ cdScaleTieR D.cd D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAtScale (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    1 ≤ p → 1 ≤ q →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (3 * p * q * StandardLattice.lamAbs lam) ^ (p * q)

theorem theorem_three_explicit_iff_scale (D : D7) : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D ↔ DiscreteSeriesDegreeBoundsAtScale D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAllScales : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), cdScaleTieR cd s → DiscreteSeriesDegreeBoundsAtScale s

theorem theorem_three_under_scale_of_general (h : DiscreteSeriesDegreeBoundsAllScales) (D : D7) : DiscreteSeriesDegreeBoundsOfScaleAgreement D := fun hT => (theorem_three_explicit_iff_scale D).mpr (h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT))

variable {eps : ℝ}

end Formalism.MainNotions.RT

end
