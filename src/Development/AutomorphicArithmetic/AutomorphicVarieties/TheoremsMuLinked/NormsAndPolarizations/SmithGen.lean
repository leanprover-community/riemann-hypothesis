module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.G6Decomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.smith_gen {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (P : GL (Fin n) K) : ∃ (U V : GL (Fin n) K) (d : Fin n → K),
      (∀ i j, ‖(U : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((U⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖(V : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((V⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) K) = U * diagonal d * V :=
  _root_.UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen P

theorem UpperTheory.V.Th.Nm.smith :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (P : GL (Fin n) (Qbar l)), ∃ (U V : GL (Fin n) (Qbar l)) (d : Fin n → Qbar l), IntM (U : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((U⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM (V : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) (Qbar l)) = U * diagonal d * V := by
  intro l _ n P
  exact smith_gen P
