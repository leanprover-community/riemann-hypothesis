module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.TateTwists.EtaleTwistedCupProductGradedCommutative
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a

def LateralTheory.EtaleFoundations.cc_flip_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν

def LateralTheory.EtaleFoundations.cc_twpair : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair (htw : LateralTheory.EtaleFoundations.cc_twpair) (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
    (a : Ht q E n i) (b : Ht q E m j) (k : ℤ) (hk : j + i = k)
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hν : IsTwPair ν) (w : ℤ) (hw : m + n = w) :
    ν.cup E hw b a = (cup q b a).cast hw hk := by
  subst hk hw
  obtain ⟨h1, h2⟩ := htw q j i
  have := h2 (j + i) rfl ν (twPair q j i) hν h1 E (n := m) (m := n) rfl
  rw [this]
  rfl

theorem LateralTheory.EtaleFoundations.etale_twisted_cup_graded_comm_of_flip_and_unique_pairing (hflip : LateralTheory.EtaleFoundations.cc_cup_flip) (hex : LateralTheory.EtaleFoundations.cc_flip_ex)
    (htw : LateralTheory.EtaleFoundations.cc_twpair) : LateralTheory.EtaleFoundations.EtaleTwistedCupProductGradedCommutative := by
  intro q _ E n m i j a b
  obtain ⟨ν, hν⟩ := hex (ZMod q) (twPair q i j)
  have hνtw : IsTwPair ν := by
    intro U ζ
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [this, (htw q i j).1 U ζ]
    simp
  have e1 : cup q a b = (n * m).negOnePow • ν.cup E (add_comm m n) b a :=
    hflip (ZMod q) (twPair q i j) ν hν E rfl (add_comm m n) a b
  rw [e1, LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair htw q E a b (i + j) (add_comm j i) ν hνtw (n + m) (add_comm m n)]
