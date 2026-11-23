module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitCoboundaryOfMulCocycle
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem _root_.GlobalTheory.T.exists_unit_coboundary_of_cocycle_addMonoidAlgebra : ∀ (B : Type) [CommRing B] (I : Ideal B), IsNilpotent I → ∀ (X : Type) [AddCommGroup X] (f : AddMonoidAlgebra B (X × X)), (∀ p, (f - 1).coeff p ∈ I) → AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) f * AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) f = AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) f * AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) f → ∃ g : (AddMonoidAlgebra B X)ˣ, (∀ x, (g.val - 1).coeff x ∈ I) ∧ f * AddMonoidAlgebra.mapDomain (fun x : X => (x, x)) g.val = AddMonoidAlgebra.mapDomain (fun x : X => (x, (0 : X))) g.val * AddMonoidAlgebra.mapDomain (fun x : X => ((0 : X), x)) g.val := by
  first | exact @GlobalTheory.exists_unit_coboundary_of_mul_cocycle | exact GlobalTheory.exists_unit_coboundary_of_mul_cocycle | (intros; apply GlobalTheory.exists_unit_coboundary_of_mul_cocycle <;> assumption)
