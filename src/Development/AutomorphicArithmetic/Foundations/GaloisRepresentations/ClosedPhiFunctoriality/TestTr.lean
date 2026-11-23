module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.testTr_holds :
    TestTr := by
  intro l _ P AI T d s v v₀ t p hv h lam
  subst hv
  let Λ : OB P →ₗ[↥(MaximalUnramifiedExtension l)] Bst P :=
    (TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P)).toLinearMap ∘ₗ lam.rTensor (Bst P)
  have hΛ : ∀ (x : Om l) (b : Bst P), Λ (x ⊗ₜ b) = lam x • b := by
    intro x b
    change TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P) (lam.rTensor (Bst P) (x ⊗ₜ b)) = lam x • b
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h1 := congrArg Λ h

  rw [map_sum, hΛ] at h1
  simp only [hΛ] at h1
  have hc : lam p • (1 : Bst P) = Polynomial.C (lam p • (1 : P.R.B)) := by
    rw [← Polynomial.smul_C, map_one]
  have h2 : (∑ i, lam (t i) • T.eB.symm (v₀ i)) = lam p • (1 : P.R.B) := by
    apply Polynomial.C_injective

    rw [map_sum, ← hc, ← h1]
    simp only [Polynomial.smul_C]
  simp only [Algebra.smul_def] at h2
  have h3 := congrArg T.eB h2

  simp only [map_sum, map_mul, map_one, mul_one, RingEquiv.apply_symm_apply] at h3
  have h4 : ∑ i, uB T (lam (t i)) * v₀ i = uB T (lam p) := h3
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
