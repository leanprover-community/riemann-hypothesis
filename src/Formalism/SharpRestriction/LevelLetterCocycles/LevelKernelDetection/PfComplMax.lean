module

public import Formalism.SharpRestriction.LevelLetterCocycles.TeichOnto
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open IsLocalRing

namespace ComplMaxPf

variable {R : Type} [CommRing R]

theorem isAdicComplete_of_pow {I J : Ideal R} (e : ℕ) (he : 1 ≤ e) (h1 : ∀ k, J ^ (e * k) ≤ I ^ k)
    (h2 : ∀ k, I ^ k ≤ J ^ k) (hI : IsAdicComplete I R) : IsAdicComplete J R := by
  have m1 : ∀ k, (J ^ (e * k) • ⊤ : Submodule R R) ≤ I ^ k • ⊤ := fun k => Submodule.smul_mono_left (h1 k)
  have m2 : ∀ k, (I ^ k • ⊤ : Submodule R R) ≤ J ^ k • ⊤ := fun k => Submodule.smul_mono_left (h2 k)
  refine { haus' := fun x hx => hI.haus' x fun k => SModEq.mono (m1 k) (hx (e * k)),
           prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.prec' (fun k => f (e * k)) fun {m n} hmn =>
    SModEq.mono (m1 m) (hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := Nat.le_mul_of_pos_left n he
  exact (hf hn).trans (SModEq.mono (m2 n) (hL n))

end ComplMaxPf

theorem complMax_holds : ComplMax := by
  intro O _ _ _ p hpm hp0 hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      rw [pow_zero, mul_one] at hu
      rw [hu] at hpm
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm u.isUnit
    · exact h
  have hIk : ∀ k, Ideal.span {(p : O)} ^ k = maximalIdeal O ^ (e * k) := fun k => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow k)]
  refine ComplMaxPf.isAdicComplete_of_pow e he (fun k => (hIk k).ge) (fun k => ?_) hc
  rw [hIk k]
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left k he)

end Formalism.MainNotions.N.Ln03.Pf
