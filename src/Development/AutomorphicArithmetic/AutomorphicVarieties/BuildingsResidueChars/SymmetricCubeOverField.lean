module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem key {R : Type} [Field R] {g s t : M2 R} {x y : R} (h : g * t = s * g) (hg0 : g 0 0 ≠ 0)
    (hg : g 1 1 = 1 ∧ g 0 1 = 0) (hs : s 1 1 = 1 ∧ s 0 1 = 0) (ht : t 1 1 = 1 ∧ t 0 1 = 0) (hne : s 0 0 ≠ 1)
    (hx : t 1 0 + t 1 1 * x = (t 0 0 + t 0 1 * x) * x) (hy : s 1 0 + s 1 1 * y = (s 0 0 + s 0 1 * y) * y) :
    g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y = 0 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hs.1, hs.2, ht.1, ht.2] at h0 h1 hx hy ⊢
  have e : t 0 0 = s 0 0 := mul_left_cancel₀ hg0 (by linear_combination h0)
  rw [e] at h1 hx
  refine mul_left_cancel₀ (sub_ne_zero.2 hne) ?_
  linear_combination h1 - hx + g 0 0 * hy
