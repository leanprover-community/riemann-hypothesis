module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs

@[expose] public section

open UpperTheory.HF

open NumberField IsDedekindDomain Formalism.HC Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory
open scoped Pointwise

private theorem exists_place {L : Type} [Field L] [NumberField L] {p : ℕ} (hs : SplitsC L p) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  unfold SplitsC at hs
  exact Set.nonempty_of_ncard_ne_zero (hs ▸ Module.finrank_pos.ne')

private theorem pow_sub_one_mem {L : Type} [Field L] [NumberField L] {p : ℕ} (v : HeightOneSpectrum (𝓞 L))
    (hN : Ideal.absNorm v.asIdeal = p) {x : 𝓞 L} {m : ℕ} (hm : m ≠ 0) (hx : x ^ m = 1) :
    x ^ (p - 1) - 1 ∈ v.asIdeal := by
  have := v.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  let := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
  have hc : Fintype.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h0 : Ideal.Quotient.mk v.asIdeal x ≠ 0 := by
    intro h
    have h1 := congrArg (Ideal.Quotient.mk v.asIdeal) hx
    rw [map_pow, h, zero_pow hm, map_one] at h1
    exact zero_ne_one h1
  rw [← Ideal.Quotient.eq, map_pow, map_one, ← hc]
  exact FiniteField.pow_card_sub_one_eq_one _ h0
