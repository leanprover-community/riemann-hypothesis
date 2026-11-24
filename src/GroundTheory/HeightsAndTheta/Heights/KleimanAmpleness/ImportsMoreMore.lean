module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def DoubleCech.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (N : ℕ)
    (x : Fin (N + 1) → Ω) (T : Kleiman.SubSystem F x Ω) (B : (∀ k, Finset (ι k)) → Submodule F Ω)
    (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ j, x j ≠ 0) →
    (∀ I, ¬ CellMeets y I → B I = ⊥) →
    (∀ J I, ¬ CellMeets y I → M J I = ⊥) →
    (∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I) →
    (∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I)) →
    (∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) →
    ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellHOf F y B n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
