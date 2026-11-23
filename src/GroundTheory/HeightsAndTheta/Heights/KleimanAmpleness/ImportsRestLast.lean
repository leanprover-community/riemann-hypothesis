module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
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

def RestrictGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (N : ℕ) (Ω : Type) [Field Ω] [Algebra F Ω] (x : Fin (N + 1) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (x' : Fin (N + 1) → K') (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0)
    (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
    (∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      ∃ h : aeval x f / aeval x g ∈ R, σ ⟨_, h⟩ = aeval x' f / aeval x' g) →
    ∀ (Q : Kleiman.LineBundle F x) (Q' : Kleiman.LineBundle F x') (c : ℤ) (H : Set Ω) (ρ : Ω → K') (w : Ω)
      (w' : K'), w' ≠ 0 →
      (∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I = Submodule.span (Kleiman.chartRing F x I) H) →
      (∀ I, (Q'.toSubSystem.twist (Kleiman.twistSys F x' c)).sub I =
        Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)) →
      (∀ h ∈ H, ∃ hh : h * w ∈ R, σ ⟨_, hh⟩ = ρ h * w') →
      ∃ r : Ω → K', Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
