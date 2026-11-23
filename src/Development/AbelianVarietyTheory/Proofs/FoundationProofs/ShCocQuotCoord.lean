module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.KA

theorem shCoc_quot_coord : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ν : G ℚ Ω → (Qbar l)ˣ)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (m : ℕ),
    GlobalTheory.KA.ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l m)⁻¹ (Y m) →
    (∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) →
    ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
      Y m (s * t) x 1 = Y m s x 1 + (ν s : Qbar l) * Y m t (x * (cycMod ℚ Ω l m s)⁻¹) 1 := by
  intro l _ Ω _ _ A ρ ν Y m hY hρ s hs t _ x
  simpa only [Pi.add_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, (hρ s hs).1,
    (hρ s hs).2, zero_mul, zero_add, MonoidHom.inv_apply] using congrFun (hY s t x) 1

end GlobalTheory.KA
