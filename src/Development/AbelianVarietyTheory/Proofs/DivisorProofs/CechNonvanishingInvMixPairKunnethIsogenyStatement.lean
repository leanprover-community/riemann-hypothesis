module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogeny
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  first | exact @GlobalTheory.AmpleGen.nv_mix_pair_of_nv | exact GlobalTheory.AmpleGen.nv_mix_pair_of_nv | (intros; apply GlobalTheory.AmpleGen.nv_mix_pair_of_nv <;> assumption)
