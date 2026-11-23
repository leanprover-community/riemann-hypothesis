module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  first | (exact @GlobalTheory.EtC.disc_elt_cls) | (exact GlobalTheory.EtC.disc_elt_cls) | (intros; apply GlobalTheory.EtC.disc_elt_cls <;> assumption)
