module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhood
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

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  first | (exact @GlobalTheory.HilbAff.exists_basic_nhd) | (exact GlobalTheory.HilbAff.exists_basic_nhd) | (intros; apply GlobalTheory.HilbAff.exists_basic_nhd  <;> assumption)
