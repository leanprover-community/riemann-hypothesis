module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
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

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ a, Fintype (ι a)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ a, ι a) → Ω) (d : ℕ)
    (μs : Fin d → K → ℤ),
    (∀ a, ∃ i, y ⟨a, i⟩ ≠ 0) → FieldNumbers.relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    ∃ (N : ℕ) (eqv : (∀ a, ι a) ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω)
      (Ms : Fin d → Kleiman.LineBundle F x),
      (∀ i, x (eqv i) = ∏ a, y ⟨a, i a⟩) ∧
      Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d ∧
      (∀ j (c : ℤ), ((Ms j).twist (Kleiman.twistSys F x c)).secs =
        secOver F y (μs j + fun _ => c)) ∧
      (∀ j, Kleiman.Nef (Ms j).toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y (μs j)) ∧
      Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun j => (Ms j).toSubSystem) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
