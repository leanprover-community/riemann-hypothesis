module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.frob :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (k : ℕ),
      InPow 1 ((g - 1) ^ l ^ k) ↔ InPow 1 (g ^ l ^ k - 1) := by
  intro l _ X _ _ g k
  have hpoly : (Polynomial.C (l : ℤ)) ∣
      ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      rw [sub_pow_char_pow, one_pow, sub_self]
    have hc := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 hc
  obtain ⟨Q, hQ⟩ := hpoly
  have key : (g - 1) ^ l ^ k - (g ^ l ^ k - 1) = (l : Module.End ℤ_[l] X) * Polynomial.aeval g Q := by
    have := congrArg (Polynomial.aeval g) hQ
    simpa using this
  have step : ∀ f f' : Module.End ℤ_[l] X, (∃ h : Module.End ℤ_[l] X, f - f' = (l : Module.End ℤ_[l] X) * h) →
      InPow 1 f' → InPow 1 f := by
    rintro f f' ⟨h, hh⟩ H x
    obtain ⟨y, hy⟩ := H x
    refine ⟨y + h x, ?_⟩
    have hf : f = (l : Module.End ℤ_[l] X) * h + f' := eq_add_of_sub_eq hh
    rw [pow_one] at hy ⊢
    rw [hf, LinearMap.add_apply, Module.End.mul_apply, Module.End.natCast_apply, hy, smul_add,
      Nat.cast_smul_eq_nsmul ℤ_[l] l (h x), add_comm]
  constructor
  · exact step _ _ ⟨-Polynomial.aeval g Q, by rw [mul_neg, ← key, neg_sub]⟩
  · exact step _ _ ⟨Polynomial.aeval g Q, key⟩
