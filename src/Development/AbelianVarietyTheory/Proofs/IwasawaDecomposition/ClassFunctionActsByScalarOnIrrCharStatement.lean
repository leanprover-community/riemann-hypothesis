module

public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionActsByScalarOnIrrChar
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

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] (e : MonoidAlgebra ℂ G), (∀ x y : G, e.coeff (y * x * y⁻¹) = e.coeff x) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x := by
  first | exact @GlobalTheory.classFun_char_scalar | exact GlobalTheory.classFun_char_scalar | (intros; apply GlobalTheory.classFun_char_scalar <;> assumption)
