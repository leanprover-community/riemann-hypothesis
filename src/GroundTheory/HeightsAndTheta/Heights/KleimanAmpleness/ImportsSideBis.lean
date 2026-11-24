module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellLocSys
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
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

def RowLocCover.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      ∃ (m : ℕ) (f u : Fin m → Ω),
        (∀ l, f l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        (∀ l, u l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        ∑ l, u l * f l = 1 ∧
        ∀ l, ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I = ⊥) ∧
          (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I ≤
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I') ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l)
                (Function.update I k (insert (c k) (I k))) =
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
