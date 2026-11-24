module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def UpperTheory.V.Ws.pairJ (k : Type) [Field k] : M4 k := !![0,0,0,1; 0,0,1,0; 0,-1,0,0; -1,0,0,0]

private theorem UpperTheory.V.Ws.pairJ_sq (k : Type) [Field k] : pairJ k * pairJ k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem UpperTheory.V.Ws.pairJ_adj {k : Type} [Field k] (X : M4 k) :
    X.transpose * pairJ k = pairJ k * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]

theorem UpperTheory.V.Ws.auPair :
    ∀ {k Γ : Type} [Field k] [Group Γ] (r : Γ →* M4 k) (μ : Γ →* kˣ), (∀ g, IsGSp (μ g : k) (r g)) → ∀ c : Γ, ∃ P : GL (Fin 4) k, ∀ s : Γ, (r s).transpose * (P : M4 k) * r (c * s * c⁻¹) = (μ s : k) • (P : M4 k) := by
  intro k Γ _ _ r μ h c
  refine ⟨⟨pairJ k * r c⁻¹, -(r c * pairJ k), ?_, ?_⟩, fun s => ?_⟩
  · rw [mul_neg, mul_assoc, ← mul_assoc (r c⁻¹), ← map_mul, inv_mul_cancel, map_one, one_mul, pairJ_sq, neg_neg]
  · rw [neg_mul, mul_assoc, ← mul_assoc (pairJ k), pairJ_sq, neg_mul, one_mul, mul_neg, neg_neg, ← map_mul,
      mul_inv_cancel, map_one]
  · show (r s).transpose * (pairJ k * r c⁻¹) * r (c * s * c⁻¹) = (μ s : k) • (pairJ k * r c⁻¹)
    have e : r c⁻¹ * r (c * s * c⁻¹) = r s * r c⁻¹ := by
      rw [← map_mul, ← map_mul]; congr 1; group
    have hs : adj (r s) * r s = (μ s : k) • (1 : M4 k) := h s
    rw [mul_assoc, mul_assoc, e, ← mul_assoc, pairJ_adj, mul_assoc, ← mul_assoc (adj _), hs,
      smul_mul_assoc, one_mul, mul_smul_comm]
