module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
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

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartFrac

theorem exists_eq_div_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  intro X Ω _ ξ κ x h c hc a
  have hchart : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc, fun c' => TieArith.mem_regAt_genCpt ξ h.gen _⟩
  obtain ⟨t, ht, hu, hta⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c (TieArith.genCpt ξ) hchart a).mp
    (TieArith.mem_regAt_genCpt ξ h.gen a)
  exact ⟨t * a, hta, t, ht, hu.1, (mul_div_cancel_left₀ a hu.1).symm⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrac
