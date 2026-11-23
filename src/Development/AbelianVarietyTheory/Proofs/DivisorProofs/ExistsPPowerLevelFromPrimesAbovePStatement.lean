module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPPowerLevelFromPrimesAboveP
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_pPower_level_from_primes_above_p : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Q : Type) [CommGroup Q] (act : D.O → Q → Q), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ a, act 1 a = a) → (∀ b c a, act (b * c) a = act b (act c a)) → (∀ b c a, act (b + c) a = act b a * act c a) → (∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l : D.La → Q, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = act c (l x)) ∧ (∀ x, l x = 1 ↔ x ∈ wSub D w r) ∧ ∀ g, (∀ c ∈ w ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g) → ∀ r : ℕ, ∃ f : D.La → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.LevCrt.exists_pLevel) | (exact GlobalTheory.UPel.HT.EtLev.LevCrt.exists_pLevel) | (intros; apply GlobalTheory.UPel.HT.EtLev.LevCrt.exists_pLevel  <;> assumption)
