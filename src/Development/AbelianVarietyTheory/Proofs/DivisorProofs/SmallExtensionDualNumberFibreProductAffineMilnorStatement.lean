module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionDualNumberFibreProductAffineMilnor
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smallExtension_dualNumber_fibreProduct_affineMilnorSquare : ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : Type) (_ : CommRing P) (i : C →+* P) (p σ : P →+* C) (q : P →+* DualNumber (IsLocalRing.ResidueField C)), p.comp i = RingHom.id C ∧ σ.comp i = RingHom.id C ∧ q.comp i = (dnInl _).comp (IsLocalRing.residue C) ∧ IsClosedImmersion (spMap σ) ∧ Surjective (spMap σ) ∧ Milnor (spMap p) (spMap σ) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) ∧ Milnor (spMap p) (spMap q) (spMap (IsLocalRing.residue C)) (spMap (dnFst _)) := by
  first | exact @GlobalTheory.DualOpen.smallExt_fibre_ring | exact GlobalTheory.DualOpen.smallExt_fibre_ring | (intros; apply GlobalTheory.DualOpen.smallExt_fibre_ring <;> assumption)
