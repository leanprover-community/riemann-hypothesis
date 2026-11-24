module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem IsTwist.mul_twist {S : Set ℕ} {ξ ξ' : HChar H.E} (h : IsTwist H S ξ) (h' : IsTwist H S ξ') :
    IsTwist H S (ξ * ξ') := by
  obtain ⟨⟨n, hn, ho⟩, ht, hl, hr⟩ := h
  obtain ⟨⟨n', hn', ho'⟩, ht', hl', hr'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ht.mul ht', fun v => HChar.LevelLe.mul (hl v) (hl' v), fun v hv => ?_⟩
  · unfold HChar.OrderDvd at *
    rw [mul_pow, pow_mul, ho, one_pow, one_mul, mul_comm n n', pow_mul, ho', one_pow]
  · by_cases h1 : ξ.UnrAt v
    · exact hr' v fun h2 => hv (h1.mul h2)
    · exact hr v h1

theorem isTwist_of_isDelta {S : Set ℕ} {p : ℕ} {δ : HChar H.E} (hp : p.Prime) (hs : SplitsC H.E p) (hS : p ∉ S)
    (h : IsDelta (H := H) p δ) : IsTwist H S δ := by
  refine ⟨h.fin, h.triv, h.tame, fun v hv => ?_⟩
  have hv' : OverP H p v := by
    by_contra hn
    exact hv (h.unr v hn)
  obtain ⟨h1, h2, h3, -⟩ := splitsC_main R H p hp hs v hv'
  rw [h1]
  exact ⟨h3, hp, h2, hS⟩

end GlobalTheory.Mem.Chr
