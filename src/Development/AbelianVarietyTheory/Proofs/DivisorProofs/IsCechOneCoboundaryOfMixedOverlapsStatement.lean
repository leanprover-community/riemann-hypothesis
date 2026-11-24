module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlaps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

theorem _root_.GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  first | exact @GlobalTheory.KS.isCob_of_mixed | exact GlobalTheory.KS.isCob_of_mixed | (intros; apply GlobalTheory.KS.isCob_of_mixed <;> assumption)
