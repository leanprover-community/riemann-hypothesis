module

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

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueMap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∃ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n → IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) ∧
      (∀ (k : K) (f g : MvPolynomial (ι k) F) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g ≠ 0 →
        ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) g ∈ R,
          σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g) ∧
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
