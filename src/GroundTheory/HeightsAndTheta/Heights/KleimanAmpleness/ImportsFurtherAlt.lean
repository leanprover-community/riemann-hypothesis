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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc quotPart)

def ModelCechTwist.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p b : ℕ) (m c : ℤ) (i : ℕ),
        Nonempty ((((Kleiman.twistMul Q.toSubSystem p m).pow b).twist
            (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).H i ≃ₗ[F]
          cechHc ι (quotPart F (mIdealOver F y)) (b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
