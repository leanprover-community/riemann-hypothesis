module

public import Development.EtaleCohomology.TateTwists.EtaleTwistedCupProductAssociative
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_twpair_ex : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def t_pair_assoc : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {i j l k₁ k₂ k : ℤ} (_ : i + j = k₁) (_ : j + l = k₂) (_ : i + k₂ = k)
    (μ₁ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k₁)))
    (μ₂ : Pair (res _ (tw q k₁)) (res _ (tw q l)) (res _ (tw q k)))
    (ν₁ : Pair (res _ (tw q j)) (res _ (tw q l)) (res _ (tw q k₂)))
    (ν₂ : Pair (res _ (tw q i)) (res _ (tw q k₂)) (res _ (tw q k))),
    IsTwPair μ₁ → IsTwPair μ₂ → IsTwPair ν₁ → IsTwPair ν₂ →
    ∀ {n m p s₁ s₂ s : ℤ} (h₁ : n + m = s₁) (h₂ : s₁ + p = s) (h₃ : m + p = s₂) (h₄ : n + s₂ = s)
      (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E p l),
      μ₂.cup E h₂ (μ₁.cup E h₁ a b) c = ν₂.cup E h₄ a (ν₁.cup E h₃ b c)

theorem cast_pair_cup {q : ℕ} {E : Spc} {i j k k' n m s s' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (hk : n + m = s) (hs : s = s')
    (a : Ht q E n i) (b : Ht q E m j) :
    Ht.cast hs e (μ.cup E hk a b : Ht q E s k) = (e ▸ μ : Pair _ _ (res _ (tw q k'))).cup E (hk.trans hs) a b := by
  subst e; subst hs; rfl

theorem isTwPair_cast {q : ℕ} {i j k k' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (h : IsTwPair μ) :
    IsTwPair (e ▸ μ : Pair _ _ (res _ (tw q k'))) := by
  subst e; exact h

theorem etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (hex : t_twpair_ex) (has : t_pair_assoc) : EtaleTwistedCupProductAssociative := by
  intro q _ E n m k i j l a b c
  have hp : ∀ i j : ℤ, IsTwPair (twPair q i j) := fun i j => pick_spec (hex q i j)
  have e : i + (j + l) = i + j + l := by ring
  have hs : n + (m + k) = n + m + k := by ring
  show (twPair q (i + j) l).cup E rfl ((twPair q i j).cup E rfl a b) c =
    Ht.cast hs e ((twPair q i (j + l)).cup E rfl a ((twPair q j l).cup E rfl b c))
  rw [cast_pair_cup]
  exact has q E rfl rfl e _ _ _ _ (hp i j) (hp (i + j) l) (hp j l) (isTwPair_cast _ e (hp i (j + l)))
    rfl rfl rfl (rfl.trans hs) a b c

end LateralTheory.EtaleFoundations
