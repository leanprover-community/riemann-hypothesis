module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem isAlgebraic_snd_of_equation {k L : Type} [Field k] [Field L] [Algebra k L] (A : WeierstrassCurve k)
    (x : k) {y : L} (h : (A.baseChange L).toAffine.Equation (algebraMap k L x) y) : IsAlgebraic k y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  refine IsIntegral.isAlgebraic ⟨Polynomial.X ^ 2 + (Polynomial.C (A.a₁ * x + A.a₃) * Polynomial.X
    - Polynomial.C (x ^ 3 + A.a₂ * x ^ 2 + A.a₄ * x + A.a₆)), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, map_add, map_mul, map_pow]
    linear_combination h

theorem isAlgebraic_snd_adjoin {k : Type} [Field k] [Algebra k ℂ] (A : WeierstrassCurve k)
    {x y : ℂ} (h : (A.baseChange ℂ).toAffine.Equation x y) : IsAlgebraic k⟮x⟯ y := by
  refine isAlgebraic_snd_of_equation (A.baseChange k⟮x⟯) (IntermediateField.AdjoinSimple.gen k x) ?_
  have e : (A.baseChange k⟮x⟯).baseChange ℂ = A.baseChange ℂ := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
  rw [e]
  exact h

theorem isAlgebraic_of_torsionCoords_finite :
    ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) (n : ℕ),
      (torsionCoords (A.baseChange ℂ) n).Finite → ∀ z ∈ torsionCoords (A.baseChange ℂ) n, IsAlgebraic ℚ z := by
  rintro F _ A n hfin z ⟨x, y, h, h0, hz⟩
  have hy : IsAlgebraic (↥F)⟮x⟯ y := isAlgebraic_snd_adjoin A h.1
  have hx : IsAlgebraic F x :=
    GlobalTheory.CurveAlgebraic.isAlgebraic_of_torsion A.toAffine (A.baseChange ℂ).toAffine rfl n _ hfin
      (fun x y h h0 => ⟨x, y, h, h0, Or.inl rfl⟩) h h0 hy
  have : FiniteDimensional F (↥F)⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  have hy' : IsAlgebraic F y := hy.restrictScalars F
  rcases hz with rfl | rfl
  · exact hx.restrictScalars ℚ
  · exact hy'.restrictScalars ℚ

end GlobalTheory.Mem.FieldsEx
