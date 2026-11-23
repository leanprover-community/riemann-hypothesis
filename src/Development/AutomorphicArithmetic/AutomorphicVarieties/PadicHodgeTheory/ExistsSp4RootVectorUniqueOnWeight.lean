module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private def rootEnt (a b i j : Fin 4) : ℤ :=
  if i = a ∧ j = b then 1 else if j.rev = a ∧ i.rev = b then -(sgn i * sgn j) else 0

private theorem rootEnt_adj : ∀ a b i j : Fin 4, a ≠ b →
    (sgn i * sgn j) * rootEnt a b j.rev i.rev = -rootEnt a b i j := by decide

private theorem rootEnt_zero : ∀ a b i j : Fin 4, wt i j ≠ wt a b → rootEnt a b i j = 0 := by decide

private theorem rootEnt_cases : ∀ a b i j : Fin 4, a ≠ b → wt i j = wt a b →
    (i = a ∧ j = b) ∨ (j.rev = a ∧ i.rev = b ∧ rootEnt a b i j = -(sgn i * sgn j)) := by decide

theorem UpperTheory.exists_sp4_root_vector_unique_on_weight :
    ∀ (E : Type) [Field E] [CharZero E] (a b : Fin 4), a ≠ b → ∃ X ∈ sp4 E, X a b = 1 ∧ (∀ i j, wt i j ≠ wt a b → X i j = 0) ∧ ∀ Y ∈ sp4 E, ∀ i j, wt i j = wt a b → Y i j = Y a b * X i j := by
  intro E _ _ a b hab
  refine ⟨Matrix.of fun i j => ((rootEnt a b i j : ℤ) : E), ?_, ?_, ?_, ?_⟩
  · show UpperTheory.V.GradeZeroInterpolatingElement.adj _ = -_
    ext i j
    rw [adj_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, zsmul_eq_mul, ← Int.cast_mul,
      rootEnt_adj a b i j hab, Int.cast_neg]
  · simp [rootEnt]
  · intro i j h
    simp [rootEnt_zero a b i j h]
  · intro Y hY i j h
    rcases rootEnt_cases a b i j hab h with ⟨rfl, rfl⟩ | ⟨h1, h2, h3⟩
    · simp [rootEnt]
    · have hY' : UpperTheory.V.GradeZeroInterpolatingElement.adj Y = -Y := hY
      have h4 := congrFun (congrFun hY' i) j
      rw [adj_apply, Matrix.neg_apply, h1, h2, zsmul_eq_mul] at h4
      rw [Matrix.of_apply, h3, Int.cast_neg]
      linear_combination h4
