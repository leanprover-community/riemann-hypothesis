module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegree
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

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | exact GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg; all_goals assumption)
