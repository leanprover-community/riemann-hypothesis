module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveWeightSection
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem _root_.GlobalTheory.T.torsion_of_generating_section : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R) (N : ℕ), 3 ≤ N → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GObj gb N s), ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (exact GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one <;> assumption)
