module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosed
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

open IsLocalRing

theorem _root_.GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ c : CommRing.Pic B, ∃ d, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.pic_divisible) | (exact GlobalTheory.PicDiv.pic_divisible) | (intros; apply GlobalTheory.PicDiv.pic_divisible  <;> assumption)
