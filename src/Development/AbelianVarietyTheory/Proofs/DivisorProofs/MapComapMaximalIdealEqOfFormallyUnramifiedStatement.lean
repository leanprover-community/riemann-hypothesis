module

public import Mathlib.RingTheory.Unramified.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapMaximalIdealEqOfFormallyUnramified
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.map_comap_maximalIdeal_eq_of_formallyUnramified' : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B], ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  first | exact @GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | exact GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | (intros; apply GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified <;> assumption)
