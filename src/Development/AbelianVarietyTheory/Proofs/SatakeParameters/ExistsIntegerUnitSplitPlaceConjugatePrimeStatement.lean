module

public import ReciprocityTheory.Automorphisms.Unitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧ Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by
  first | exact @GlobalTheory.SplitSep.exists_sep | exact GlobalTheory.SplitSep.exists_sep | (intros; apply GlobalTheory.SplitSep.exists_sep <;> assumption)
