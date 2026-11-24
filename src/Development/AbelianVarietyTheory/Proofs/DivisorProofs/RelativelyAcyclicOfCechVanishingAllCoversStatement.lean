module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAcyclicOfCechVanishingAllCovers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.relativelyAcyclic_of_cech_vanishing_all_covers : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left), (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  first | exact @GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | exact GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | (intros; apply GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV <;> assumption)
