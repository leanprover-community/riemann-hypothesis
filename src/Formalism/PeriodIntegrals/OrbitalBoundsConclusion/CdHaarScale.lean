module

public import Formalism.PeriodIntegrals.CdHaarScale
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarScaling.MapEqSelfOfIterate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory MeasureTheory.Measure PI.UnitaryGroupMassFormula.CdHaarScale.Main

theorem cd_haar_scaling : PI.CdHaarScale := by
  intro cd n ε
  by_cases hex : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false)
  · obtain ⟨P₀, Q₀, e₀, h1₀, h2₀⟩ := hex
    have key : ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
        (h2 : ∀ j, ε (e (Sum.inr j)) = false),
        (cd.cd P Q).map (phi e h1 h2) = (cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀) := by
      intro P Q e h1 h2
      have hP : P = P₀ := (card_true e h1 h2).symm.trans (card_true e₀ h1₀ h2₀)
      have hQ : Q = Q₀ := (card_false e h1 h2).symm.trans (card_false e₀ h1₀ h2₀)
      subst hP hQ
      have := cd.haar P Q
      exact map_phi_indep e₀ e h1₀ h2₀ h1 h2 (cd.cd P Q)
    have := cd.haar P₀ Q₀
    have hν : (cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀) =
        haarScalarFactor ((cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀)) (Formalism.REAL.muG ε) • Formalism.REAL.muG ε :=
      isMulLeftInvariant_eq_smul _ _
    refine ⟨haarScalarFactor ((cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀)) (Formalism.REAL.muG ε),
      haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
    intro P Q e h1 h2 A hA
    have hp : Measurable (⇑(phi e h1 h2)) := (phi e h1 h2).continuous.measurable
    rw [tie_set e h1 h2 A, ← Measure.map_apply hp hA, key P Q e h1 h2]
    conv_rhs => rw [hν]
    rw [ENNReal.smul_def]
  · refine ⟨1, one_pos, ?_⟩
    intro P Q e h1 h2
    exact absurd ⟨P, Q, e, h1, h2⟩ hex
