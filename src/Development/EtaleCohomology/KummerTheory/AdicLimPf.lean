module

public import Development.EtaleCohomology.KummerTheory.AdicDegPf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def AdicKer : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ (n : ℤ) (k : ℕ) (x : Hl l E n i), lev l x k = 0 →
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y

def AdicFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), (∀ k : ℕ, Finite (Ht (l ^ k) E n i)) →
  (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) →
    Module.Finite ℤ_[l] (Hl l E n i)

def AdicCok : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l E (n + 1) i) →
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z

theorem AdicLim_of (hK : AdicKer) (hF : AdicFin) (hC : AdicCok) : AdicLim := by
  intro hA l _ E i hB hFin n
  have hker : ∀ m : ℤ, ∀ (k : ℕ) (x : Hl l E m i), lev l x k = 0 → ∃ y : Hl l E m i, x = ((l : ℤ_[l]) ^ k) • y :=
    fun m => hK hA l E i hB hFin m
  have hfin : ∀ m : ℤ, Module.Finite ℤ_[l] (Hl l E m i) := fun m => hF l E m i (fun k => hFin k m) (hker m)
  exact ⟨hfin n, hker n, hC hA l E i hB hFin n (hfin (n + 1))⟩

end LateralTheory.KummerTheory
