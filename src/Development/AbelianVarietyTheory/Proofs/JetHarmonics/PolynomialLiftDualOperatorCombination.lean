module

public import Formalism.RealPlaceAnalysis.StatementE
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.HermitianCurvature.StatementQ
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.LevelRecursionCondNeeded
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementR
import Formalism.HermitianCurvature.StatementWd
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Mathlib.Tactic.Linter.Style
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinor, Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient, Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec, Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit, Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite, Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombination

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinor =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinor", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.StatementE\npublic import Mathlib.LinearAlgebra.Matrix.Determinant.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Jets.SameFns\nimport Formalism.FormalDegreeBessel.StatementWR\nimport Formalism.HermitianCurvature.StatementFr\nimport Formalism.HermitianCurvature.StatementI\nimport Formalism.HermitianCurvature.StatementR\nimport Formalism.HermitianCurvature.StatementWd\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.ScalarColsMinor

noncomputable def bord {p m : ℕ} (M : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m)) :
    Matrix (Fin (p + m)) (Fin (p + m)) ℂ :=
  Matrix.of fun a : Fin (p + m) => Fin.append (M a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)

theorem det_bord {p m : ℕ} (M : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m)) :
    (bord M c).det = ∑ σ : Equiv.Perm (Fin (p + m)),
      if (fun k => σ (Fin.natAdd p k)) = c then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, M (σ (Fin.castAdd m k)) k else 0 := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fin.prod_univ_add]
  simp only [bord, Matrix.of_apply, Fin.append_left, Fin.append_right]
  rw [Finset.prod_boole]
  by_cases h : (fun k => σ (Fin.natAdd p k)) = c
  · rw [if_pos h, if_pos (fun k _ => congrFun h k), mul_one]
  · rw [if_neg h, if_neg (fun hh => h (funext fun k => hh k (Finset.mem_univ _)))]
    simp

theorem sum_perm_eq {A : Type} [AddCommGroup A] [Module ℂ A] {p m : ℕ}
    (M : Matrix (Fin (p + m)) (Fin p) ℂ) (F : (Fin m → Fin (p + m)) → A) :
    ∑ σ : Equiv.Perm (Fin (p + m)),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, M (σ (Fin.castAdd m k)) k) •
        F (fun k => σ (Fin.natAdd p k)) = ∑ c, (bord M c).det • F c := by
  simp only [det_bord, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp

theorem det_bord_mul {p m : ℕ} (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ)
    (c : Fin m → Fin (p + m)) : (bord (Λ * N) c).det = N.det * (bord Λ c).det := by
  have h : bord (Λ * N) c = bord Λ c * (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks N 0 0 (1 : Matrix (Fin m) (Fin m) ℂ))) := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp [bord, Matrix.mul_apply]
    · simp [bord, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    mul_comm]

theorem det_bord_perm {p m : ℕ} (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m))
    (τ : Equiv.Perm (Fin m)) :
    (bord Λ (fun k => c (τ k))).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (bord Λ c).det := by
  have h : bord Λ (fun k => c (τ k)) = (bord Λ c).submatrix id
      (finSumFinEquiv.permCongr (Equiv.sumCongr (1 : Equiv.Perm (Fin p)) τ)) := by
    ext a b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp [bord]
    · simp [bord]
  rw [h, Matrix.det_permute', Equiv.Perm.sign_permCongr]
  have := Equiv.Perm.sign_sumCongr (1 : Equiv.Perm (Fin p)) τ
  simp only [Equiv.Perm.sumCongr] at this
  rw [this]
  simp

theorem prod_ofFn_sum {A : Type} [Ring A] [Algebra ℂ A] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℂ)
    (T : Fin m → Fin n → A) :
    (List.ofFn fun k => ∑ d, Q k d • T k d).prod =
      ∑ d : Fin m → Fin n, (∏ k, Q k (d k)) • (List.ofFn fun k => T k (d k)).prod := by
  have h := (MultilinearMap.mkPiAlgebraFin ℂ m A).map_sum (fun k d => Q k d • T k d)
  simp only [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply] at h
  exact h

theorem sum_det_qminor {A : Type} [Ring A] [Algebra ℂ A] {p m : ℕ} (E : Fin (p + m) → Fin (p + m) → A)
    (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (d : Fin m → Fin (p + m)) (w : ℂ) :
    ∑ c : Fin m → Fin (p + m), (bord Λ c).det • qminor E c d w =
      ((m.factorial : ℕ) : ℂ) • ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
  simp only [qminor, Finset.smul_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))]
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin m), ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
      (((Equiv.Perm.sign τ : ℤ) : A) *
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c (τ k)) (d k)).prod) =
      ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
    intro τ
    refine Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl _)) _ _ fun c => ?_
    have hc : (Equiv.arrowCongr τ.symm (Equiv.refl _)) c = fun k => c (τ k) := by
      ext k; simp
    rw [hc, det_bord_perm, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl fun τ _ => h τ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul]

theorem antisym_prod_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin m) (Fin (p + m)) ℂ) (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ) (w : ℂ), ∑ σ : Equiv.Perm (Fin (p + m)), (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, (Λ * N) (σ (Fin.castAdd m k)) k) • (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m), ((Matrix.of fun a : Fin (p + m) => Fin.append (Λ a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w := by
  intro A _ _ p m E Q Λ N w
  have h1 := sum_perm_eq (Λ * N) (fun c : Fin m → Fin (p + m) =>
    (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (c k) d).prod)
  rw [h1]
  change _ = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m),
    ((bord Λ c).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w
  rw [Finset.sum_comm]
  have hf : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h2 : ∀ d : Fin m → Fin (p + m), ∑ c : Fin m → Fin (p + m),
      ((bord Λ c).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w =
      ∑ c : Fin m → Fin (p + m), (bord Λ c).det • (∏ k, Q k (d k)) •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
    intro d
    simp only [mul_comm (bord Λ _).det, mul_smul]
    rw [← Finset.smul_sum, ← Finset.smul_sum, sum_det_qminor, smul_smul _ ((m.factorial : ℕ) : ℂ),
      inv_mul_cancel₀ hf, one_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _
  rw [Finset.sum_congr rfl fun d _ => h2 d, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [det_bord_mul, mul_smul, prod_ofFn_sum Q (fun k d => Tm E (w - ((k : ℕ) : ℂ)) (c k) d),
    Finset.smul_sum (r := (bord Λ c).det)]

end GlobalTheory.ScalarColsMinor
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinor =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Jets.SameFns\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.CapelliTop

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem prod_ofFn_sum_smul {t n : ℕ} (q : Fin t → Fin n → ℂ) (x : Fin t → Fin n → A) :
    (List.ofFn fun k : Fin t => ∑ d, q k d • x k d).prod =
      ∑ d : Fin t → Fin n, (∏ k, q k (d k)) • (List.ofFn fun k => x k (d k)).prod := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply]
  simp only [RingHom.id_apply]

theorem qminor_eq_zero {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (d : Fin n → Fin n)
    (hd : ¬ Function.Injective d) (u : ℂ) : qminor E id d u = 0 := by
  simp only [Function.Injective, not_forall] at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have h := quantumMinorColSkew_holds A n n E hE id d (Equiv.swap i j) u
  have e : d ∘ Equiv.swap i j = d := by
    funext k
    exact Equiv.apply_swap_eq_self hij k
  rw [e, Equiv.Perm.sign_swap hne] at h
  apply eq_zero_of_add_self_eq_zero
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  exact add_eq_zero_iff_eq_neg.mpr h

theorem det_smul_qdet {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (Q : Matrix (Fin n) (Fin n) ℂ)
    (u : ℂ) : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod := by
  classical
  have h1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod =
      ∑ d : Fin n → Fin n, (∏ k, Q k (d k)) • qminor E id d u := by
    simp only [Finset.smul_sum, qminor]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [prod_ofFn_sum_smul (fun k d => Q k d) (fun k d => Tm E (u - (k : ℂ)) (σ k) d),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  rw [h1, ← Matrix.det_transpose, Matrix.det_apply', Finset.sum_smul]
  refine Fintype.sum_of_injective (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n))
    DFunLike.coe_injective _ _ ?_ ?_
  · intro d hd
    rw [qminor_eq_zero E hE d, smul_zero]
    intro hinj
    exact hd ⟨Equiv.ofBijective d (Finite.injective_iff_bijective.mp hinj), rfl⟩
  · intro τ
    have h := quantumMinorColSkew_holds A n n E hE id id τ u
    rw [Function.id_comp] at h
    rw [h, mul_comm, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl

theorem mul_pow_shift (x y δ : A) (h : x * δ = δ * (x + y)) (hy : y * δ = δ * y) (s : ℕ) :
    x * δ ^ s = δ ^ s * (x + (s : ℂ) • y) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc, add_mul, h, smul_mul_assoc, hy,
      Nat.cast_succ, add_smul, one_smul, ← mul_smul_comm, ← mul_add]
    congr 2
    abel

theorem prod_ofFn_semiconj {t : ℕ} (x y : Fin t → A) (g : A) (h : ∀ k, x k * g = g * y k) :
    (List.ofFn x).prod * g = g * (List.ofFn y).prod := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [mul_assoc, ih _ _ (fun k => h k.succ), ← mul_assoc, h, mul_assoc]

theorem pt_prod {t : ℕ} (x y : Fin t → A) :
    TL.PT t (fun s : ℂ => (List.ofFn fun k => x k + s • y k).prod) (List.ofFn y).prod := by
  induction t with
  | zero => exact (TL.PT.const 1).congr (fun s => by simp) (by simp)
  | succ t ih =>
    have h := ih (fun k => x k.succ) (fun k => y k.succ)
    refine ((h.mulL (x 0)).up.add (h.mulL (y 0)).mulS).congr (fun s => ?_) ?_
    · simp only [List.ofFn_succ, List.prod_cons, add_mul, smul_mul_assoc]
    · simp only [List.ofFn_succ, List.prod_cons, zero_add]

theorem sum_smul_Tm {n : ℕ} (E : Fin n → Fin n → A) (q : Fin n → ℂ) (u : ℂ) (a : Fin n) :
    ∑ d, q d • Tm E u a d = (q a * u) • (1 : A) + ∑ d, q d • E a d := by
  simp [shiftedGenerator_eq_ite_smul_add, Finset.sum_add_distrib, smul_smul, ite_smul]

theorem top_coefficient : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin (p + m)) (Fin (p + m)) ℂ) (δ : A) (ν : Fin (p + m) → Fin p → A) (u : ℂ), GlRel E → (∀ a k, (∑ d, Q (Fin.castAdd m k) d • E a d) * δ = δ * ((∑ d, Q (Fin.castAdd m k) d • E a d) + ν a k)) → (∀ a k, (∑ d, Q (Fin.natAdd p k) d • E a d) * δ = δ * ∑ d, Q (Fin.natAdd p k) d • E a d) → (∀ a k, ν a k * δ = δ * ν a k) → Q.det • ∑ s : Fin (p + 1), ((F7.lagCo (fun j : Fin (p + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) = δ ^ p * ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun k : Fin p => ν (σ (Fin.castAdd m k)) k).prod * (List.ofFn fun k : Fin m => ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod) := by
  intro A _ _ p m E Q δ ν u hE h1 h2 h3
  set X : Equiv.Perm (Fin (p + m)) → Fin p → A := fun σ k =>
    ∑ d, Q (Fin.castAdd m k) d • Tm E (u - ((k : ℕ) : ℂ)) (σ (Fin.castAdd m k)) d with hX
  set Y : Equiv.Perm (Fin (p + m)) → A := fun σ => (List.ofFn fun k : Fin m =>
    ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod with hY
  have e1 : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn (X σ)).prod * Y σ) := by
    rw [det_smul_qdet E hE]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [List.ofFn_add, List.prod_append]
    simp only [hX, hY, Fin.val_natAdd, Nat.cast_add, sub_sub]
    rfl
  have eY : ∀ σ (s : ℕ), Y σ * δ ^ s = δ ^ s * Y σ := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => Commute.pow_right (?_ : _ * _ = _ * _) s
    rw [sum_smul_Tm, add_mul, mul_add, h2]
    simp
  have eX : ∀ σ (s : ℕ), (List.ofFn (X σ)).prod * δ ^ s =
      δ ^ s * (List.ofFn fun k => X σ k + (s : ℂ) • ν (σ (Fin.castAdd m k)) k).prod := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => mul_pow_shift _ _ _ ?_ (h3 _ _) s
    simp only [hX]
    rw [sum_smul_Tm, add_mul, h1, add_assoc, mul_add δ (_ • _)]
    simp
  have e2 : ∀ s : Fin (p + 1), Q.det • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) =
      ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (δ ^ p *
        ((List.ofFn fun k => X σ k + ((s : ℕ) : ℂ) • ν (σ (Fin.castAdd m k)) k).prod * Y σ)) := by
    intro s
    rw [← mul_smul_comm, ← smul_mul_assoc, e1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_assoc, eY, ← mul_assoc _ (δ ^ (s : ℕ)), eX, mul_assoc,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp s.isLt)]
  rw [Finset.smul_sum, Finset.mul_sum]
  simp only [smul_comm Q.det, e2, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := (((pt_prod (X σ) (fun k => ν (σ (Fin.castAdd m k)) k)).mulR (Y σ)).mulL (δ ^ p)).lag
  rw [mul_smul_comm]
  refine Eq.trans ?_ (congrArg _ h.symm)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

end GlobalTheory.CapelliTop
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec", "h": "module\n\npublic import Formalism.FormalDegreeBessel.StatementG\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Jets.SameFns\nimport Formalism.HermitianCurvature.StatementFr\nimport Formalism.HermitianCurvature.StatementI\nimport Formalism.HermitianCurvature.StatementR\nimport Formalism.HermitianCurvature.StatementWd\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DualFrame

theorem exists_linearIndependent_extend {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent ℂ v) (m : ℕ) (hm : n + m ≤ Module.finrank ℂ V) :
    ∃ w : Fin (n + m) → V, LinearIndependent ℂ w ∧ ∀ j, w (Fin.castAdd m j) = v j := by
  induction m with
  | zero => exact ⟨v, hv, fun j => rfl⟩
  | succ m ih =>
    obtain ⟨w, hw, hwv⟩ := ih (by omega)
    have hx : ∃ x, x ∉ Submodule.span ℂ (Set.range w) := by
      by_contra h
      have htop : Submodule.span ℂ (Set.range w) = ⊤ :=
        eq_top_iff.mpr (fun x _ => by_contra (fun hx => h ⟨x, hx⟩))
      have h1 := finrank_range_le_card (R := ℂ) (b := w)
      rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx⟩ := hx
    refine ⟨Fin.snoc (α := fun _ => V) w x, linearIndependent_finSnoc.mpr ⟨hw, hx⟩, fun j => ?_⟩
    have hj : (Fin.castAdd (m + 1) j : Fin (n + (m + 1))) = Fin.castSucc (Fin.castAdd m j) := Fin.ext rfl
    rw [hj, Fin.snoc_castSucc, hwv]

theorem linearIndependent_fvec (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (h0 : z' ≠ 0) :
    LinearIndependent ℂ (fvec k r z') := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hs : ∀ d, ∑ i : Fin r, g (Fin.castSucc i) * bvec (eI k r i) d + g (Fin.last r) * z' d = 0 := by
    intro d
    have := congrFun hg d
    rw [Fin.sum_univ_castSucc] at this
    simpa [fvec] using this
  have hlast : g (Fin.last r) = 0 := by
    obtain ⟨d, hd⟩ := Function.ne_iff.mp h0
    have hd' : r ≤ d.val := by
      by_contra hlt
      exact hd (hz d (Or.inl (by omega)))
    have := hs d
    have hb : ∀ i : Fin r, bvec (eI k r i) d = 0 := by
      intro i
      have hne : d ≠ eI k r i := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, hne]
    simp only [hb, mul_zero, Finset.sum_const_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_right hd
  intro i
  refine Fin.lastCases hlast (fun a => ?_) i
  have := hs (eI k r a)
  rw [hlast, zero_mul, add_zero] at this
  rw [Finset.sum_eq_single a] at this
  · simpa [bvec] using this
  · intro b _ hb
    have hne : eI k r a ≠ eI k r b := by
      intro h
      apply hb
      have := congrArg Fin.val h
      simp [eI] at this
      exact Fin.ext this.symm
    simp [bvec, hne]
  · simp

theorem exists_dual_matrix (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)) (hz : inWb k r z') (hT : 0 < Tz k r z') :
    ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧
      (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧
      ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  have hz0 : z' ≠ 0 := by
    rintro rfl
    simp [Tz, herm] at hT
  have hli := linearIndependent_fvec k r z' hz hz0
  set u : Fin (r + 1) → Fin (r + 1 + (r + k)) → ℂ := fun j d => fvec k r z' j (e d) with hu
  have hul : LinearIndependent ℂ u :=
    hli.map' (LinearEquiv.funCongrLeft ℂ ℂ e).toLinearMap (LinearEquiv.ker _)
  obtain ⟨w, hw, hwu⟩ := exists_linearIndependent_extend u hul (r + k)
    (by rw [Module.finrank_fin_fun])
  set A : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ := Matrix.of w with hA
  have hAu : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hw
  have hdet : IsUnit A.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hQ : (A.transpose)⁻¹ * A.transpose = 1 := Matrix.nonsing_inv_mul _ hdet
  have hcol : ∀ (i : Fin (r + 1 + (r + k))) (j : Fin (r + 1)),
      ∑ d, (A.transpose)⁻¹ i d * fvec k r z' j (e d) = if i = Fin.castAdd (r + k) j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hQ i) (Fin.castAdd (r + k) j)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp [hA, hwu, hu]
  refine ⟨(A.transpose)⁻¹, ?_, fun i j => ?_, fun i j => ?_⟩
  · intro h
    have := congrArg Matrix.det hQ
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  · rw [hcol]
    simp [Fin.castAdd_inj]
  · rw [hcol]
    have : Fin.natAdd (r + 1) i ≠ Fin.castAdd (r + k) j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [this]

end GlobalTheory.HatNF.DualFrame
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementQ\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule\nimport Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt\nimport Development.AbelianVarietyTheory.Definitions.Jets.SameFns\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DetLeibniz

open Matrix QnYLeibnizW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trace_adjugate_mul_eq_sum_cramer {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A.adjugate * B).trace = ∑ j, A.cramer (fun i => B i j) j := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cramer_eq_adjugate_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem hasDerivAt_det_Zhat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g X : Q.Mx k r) :
    HasDerivAt (fun t : ℝ => (Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X))).det)
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X)).trace 0 := by
  have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X)))
    (Zhat k r z z' (g * X)) 0 (fun i j =>
      (hermL (Hpk k r) (fvec k r z' j) (fvec k r z i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasDerivAt_mul_exp_smul_zero g X))
  simp only [curve_zero] at h
  exact h

theorem Zhat_add_smul (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (A B : Q.Mx k r) (c : ℂ) :
    Zhat k r z z' (A + c • B) = Zhat k r z z' A + c • Zhat k r z z' B := by
  ext i j
  simp [Zhat, herm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul]

theorem Zhat_mul_single (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r)
    (p q : Fin (2 * r + k + 1)) (j : Fin (r + 1)) :
    (fun i => Zhat k r z z' (g * Matrix.single p q 1) i j) =
      fvec k r z' j q • fun i => herm (Hpk k r) (g *ᵥ bvec p) (fvec k r z i) := by
  have hv : Matrix.single p q (1 : ℂ) *ᵥ fvec k r z' j = fvec k r z' j q • bvec p := by
    rw [Matrix.single_mulVec]
    funext l
    by_cases h : l = p
    · subst h; simp [bvec]
    · simp [bvec, h]
  funext i
  simp only [Zhat, Pi.smul_apply, ← Matrix.mulVec_mulVec, hv, herm, Matrix.mulVec_smul, dotProduct_smul]

theorem det_leibniz : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Q.Mx k r)) (a b : Fin (Q.mdim k r 0)) (f : Q.Mx k r → E), Q.SmoothLev k r 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => (Zhat k r z z' x).det • f x) g = (Zhat k r z z' g).det • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (∑ j : Fin (r + 1), fvec k r z' j (Q.posL k r 0 b) * (Zhat k r z z' g).cramer (fun i => herm (Hpk k r) (g.mulVec (bvec (Q.posL k r 0 a))) (fvec k r z i)) j) • f g := by
  intro E _ _ k r z z' D a b f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hgG : g ∈ Q.Glev k r 0 := hg.1
  obtain ⟨hX1, hX2⟩ := hpart_mem (k := k) (r := r) (i := 0) a b
  set Z : Q.Mx k r := Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) 1 with hZdef
  set X1 := hpart1 (Hpk k r) Z with hX1def
  set X2 := hpart2 (Hpk k r) Z with hX2def
  have hf1 := hasDerivAt_f f F U g X1 hU hgU hgG hF hfF hX1
  have hf2 := hasDerivAt_f f F U g X2 hU hgU hgG hF hfF hX2
  have hEf : Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g =
      fderiv ℝ F g (g * X1) + Complex.I • fderiv ℝ F g (g * X2) := by
    show RdV X1 f g + Complex.I • RdV X2 f g = _
    rw [rdV_of_hasDerivAt X1 g f _ hf1, rdV_of_hasDerivAt X2 g f _ hf2]
  have key : ∀ (φ : Q.Mx k r → ℂ) (d1 d2 : ℂ),
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X1))) d1 0 →
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X2))) d2 0 →
      Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => φ x • f x) g =
        φ g • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (d1 + Complex.I * d2) • f g := by
    intro φ d1 d2 h1 h2
    rw [hEf]
    show RdV X1 (fun x => φ x • f x) g + Complex.I • RdV X2 (fun x => φ x • f x) g = _
    rw [rdV_smul_of X1 g φ f d1 _ h1 hf1, rdV_smul_of X2 g φ f d2 _ h2 hf2]
    module
  rw [key (fun x => (Zhat k r z z' x).det) _ _ (hasDerivAt_det_Zhat k r z z' g X1)
    (hasDerivAt_det_Zhat k r z z' g X2)]
  have hsum : g * X1 + Complex.I • (g * X2) = g * Z := by
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hX1def, hX2def, hpart_sum]
  have hd : ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X1)).trace +
      Complex.I * ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X2)).trace =
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * Z)).trace := by
    rw [← hsum, Zhat_add_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [hd, trace_adjugate_mul_eq_sum_cramer]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hZdef, Zhat_mul_single, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.HatNF.DetLeibniz
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Jets.SameFns\nimport Mathlib.Algebra.Module.StablyFree.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.RhvPoly

inductive IsPol {V : Type} [AddCommGroup V] [Module ℂ V] : (ℂ → V) → Prop
  | const (a : V) : IsPol fun _ => a
  | add {f g : ℂ → V} : IsPol f → IsPol g → IsPol fun y => f y + g y
  | xsmul {f : ℂ → V} : IsPol f → IsPol fun y => y • f y

section module

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end module

section alg

variable {A : Type} [Ring A] [Algebra ℂ A]

end alg

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_finset_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → V}
    (hf : ∀ i ∈ s, _root_.GlobalTheory.RhvPoly.IsPol (f i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (0 : V)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_pow_smul (n : ℕ) (v : V) : _root_.GlobalTheory.RhvPoly.IsPol fun y : ℂ => y ^ n • v := by
  induction n with
  | zero => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const v
  | succ n ih =>
    simp only [pow_succ', mul_smul]
    exact ih.xsmul

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eval_smul (p : Polynomial ℂ) (v : V) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => p.eval y • v := by
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_smul, mul_smul]
  refine isPol_finset_sum _ fun i _ => ?_
  convert isPol_pow_smul i (p.coeff i • v) using 1
  funext y
  exact smul_comm _ _ _

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_linearMap_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → ℂ) →ₗ[ℂ] A)
    (p : ι → Polynomial ℂ) : _root_.GlobalTheory.RhvPoly.IsPol fun y => g (fun ρ => (p ρ).eval y) := by
  have h : ∀ y : ℂ, (fun ρ => (p ρ).eval y) = ∑ ρ, (p ρ).eval y • Pi.single ρ (1 : ℂ) := by
    intro y
    ext ρ'
    simp [Finset.sum_apply, Pi.single_apply]

  simp only [h, map_sum, map_smul]
  exact isPol_finset_sum _ fun ρ _ => isPol_eval_smul _ _

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_linearMap_comp (g : V →ₗ[ℂ] W) {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => g (f y) := by
  induction hf with
  | const a => exact .const _
  | add _ _ ihf ihg => simpa only [map_add (f := _)] using ihf.add ihg
  | xsmul _ ih => simpa only [map_smul] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_mul {f g : ℂ → A} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (hg : _root_.GlobalTheory.RhvPoly.IsPol g) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => f y * g y := by
  induction hf with
  | const a => exact isPol_linearMap_comp (LinearMap.mulLeft ℂ a) hg
  | add _ _ ihf ihg => simpa only [add_mul] using ihf.add ihg
  | xsmul _ ih => simpa only [smul_mul_assoc] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_algebraMap_eval (p : Polynomial ℂ) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => algebraMap ℂ A (p.eval y) := by
  simpa [Algebra.algebraMap_eq_smul_one] using isPol_eval_smul p (1 : A)

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_list_prod {ι : Type} (l : List ι) {F : ι → ℂ → A}
    (hF : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol (F i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => (l.map fun i => F i y).prod := by
  induction l with
  | nil => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (1 : A)
  | cons a l ih => simpa using isPol_mul (hF a) ih

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_Tvprod' {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvprod y := by
  have hT : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvl y i := by
    intro i
    have : (fun y => L.Tvl y i) =
        fun y => y • !![(1 : A), 0; 0, 0] + !![-L.pb i, -L.cb i; L.cbi i, 0] := by
      funext y
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvl
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    rw [this]
    exact (_root_.GlobalTheory.RhvPoly.IsPol.const _).xsmul.add (.const _)
  have h : (fun y => L.Tvprod y) =
      fun y => ((List.finRange r).reverse.map fun i => L.Tvl y i).prod := by
    funext y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvprod
    simp [List.ofFn_eq_map, List.map_reverse]
  rw [h]
  exact isPol_list_prod _ hT

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma exists_polynomial_eq_functional_of_isPol {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (φ : V →ₗ[ℂ] ℂ) :
    ∃ p : Polynomial ℂ, ∀ y, φ (f y) = p.eval y := by
  induction hf with
  | const a => exact ⟨Polynomial.C (φ a), fun y => by simp⟩
  | add _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p + q, fun y => by simp [hp, hq]⟩
  | xsmul _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨Polynomial.X * p, fun y => by simp [hp]⟩

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eq_zero_of_infinite_zeros {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) {S : Set ℂ}
    (hS : S.Infinite) (h0 : ∀ y ∈ S, f y = 0) (y : ℂ) : f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨p, hp⟩ := exists_polynomial_eq_functional_of_isPol hf φ
  have : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    (hS.mono fun x hx => by simp [← hp, h0 x hx])
  simp [hp, this]


open MeasureTheory in
theorem _root_.GlobalTheory.RhvPoly.rhv_mem_of_infinite : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A]
    (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite →
    (∀ y ∈ S, _root_.GlobalTheory.HatNF.rhv d y ∈ K) → ∀ y : ℂ, _root_.GlobalTheory.HatNF.rhv d y ∈ K := by
  intro P A _ _ _ d K S hS hmem y
  classical
  have hx : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.x y := by
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x _root_.Formalism.FourierDecayAlt.M.xC
    simp [Polynomial.eval_prod]
  have hS12 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.S12 y := by
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.S12
    refine isPol_finset_sum _ fun l _ => isPol_mul ?_ (.const _)
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.M.xEx
    simp [Polynomial.eval_prod]
  have hm0 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.m0 y := by
    have := (_root_.GlobalTheory.RhvPoly.IsPol.const (-d.L.nabs)).add
      (isPol_linearMap_comp (LinearMap.mulRight ℂ (-(d.L.ζ * d.L.GGi)))
        (isPol_algebraMap_eval (A := A) (Polynomial.X - Polynomial.C (1 / 2))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.m0
    simp [sub_eq_add_neg]
  have hTv := isPol_Tvprod' d.L
  have hentry : ∀ i j : Fin 2, _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.Tvprod y i j :=
    fun i j => isPol_linearMap_comp (Matrix.entryLinearMap ℂ A i j) hTv
  have hpol : _root_.GlobalTheory.RhvPoly.IsPol fun y => _root_.GlobalTheory.HatNF.rhv d y := by
    have h : (fun y => _root_.GlobalTheory.HatNF.rhv d y) = fun y =>
        d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Tvprod y 0 0 +
          d.L.GG * d.x y * d.L.Tvprod y 1 0) := by
      funext y
      unfold _root_.GlobalTheory.HatNF.rhv _root_.Formalism.FourierDecayAlt.Q.NFData.QQ _root_.Formalism.FourierDecayAlt.R.LevelData.Avr _root_.Formalism.FourierDecayAlt.R.LevelData.Bvr
      simp
    rw [h]
    refine isPol_mul (.const _) (.add (isPol_mul (.add (isPol_mul (isPol_mul (.const _) hx) hm0) hS12)
      (hentry 0 0)) (isPol_mul (isPol_mul (.const _) hx) (hentry 1 0)))
  have hq := isPol_linearMap_comp K.mkQ hpol
  have := isPol_eq_zero_of_infinite_zeros hq hS
    (fun y hy => (Submodule.Quotient.mk_eq_zero K).2 (hmem y hy)) y
  exact (Submodule.Quotient.mk_eq_zero K).1 this

end GlobalTheory.RhvPoly
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombination =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombination", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain\npublic import Formalism.HermitianCurvature.StatementJF\npublic import Formalism.RealPlaceAnalysis.StatementE\npublic import Mathlib.LinearAlgebra.Matrix.Determinant.Basic\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinor\npublic import Formalism.HermitianCurvature.LevelRecursionCondNeeded\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient\npublic import Formalism.FormalDegreeBessel.StatementG\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators\npublic import Formalism.HermitianCurvature.StatementQ\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator\npublic import Development.AbelianVarietyTheory.Definitions.Jets.SameFns\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.HatNF.MirrorLift

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open scoped ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_of_poly {N κ : ℕ} {φ : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ φ) : ContDiff ℝ ∞ φ := by
  obtain ⟨q, -, hq⟩ := h
  rw [show φ = _ from funext hq]
  clear hq
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    have he : ∀ a b : Fin N, ContDiff ℝ ∞ (fun g : Matrix (Fin N) (Fin N) ℂ => g a b) := fun a b =>
      (contDiff_apply_apply ℝ a b)
    rcases i with i | i
    · exact he _ _
    · exact Complex.conjCLE.contDiff.comp (he i.1 i.2)

theorem glRel_cast {A : Type*} [Ring A] {n n' : ℕ} (h : n = n') {E : Fin n' → Fin n' → A} (hE : GlRel E) :
    GlRel (fun a b => E (Fin.cast h a) (Fin.cast h b)) := by
  subst h; exact hE

theorem qminor_cast' {A : Type*} [Ring A] [Algebra ℂ A] {n n' t : ℕ} (h : n = n') (E : Fin n' → Fin n' → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun a b => E (Fin.cast h a) (Fin.cast h b)) a b u = qminor E (Fin.cast h ∘ a) (Fin.cast h ∘ b) u := by
  subst h; rfl

theorem qdet_cast {A : Type*} [Ring A] [Algebra ℂ A] {n n' : ℕ} (h : n = n') (E : Fin n' → Fin n' → A) (u : ℂ) :
    qdet (fun a b => E (Fin.cast h a) (Fin.cast h b)) u = qminor E id id u := by
  subst h; rfl

section mul

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem good_mul (hD : IsOpen D) {φ : Q.Mx k r → ℂ} (hφ : ContDiffOn ℝ ∞ φ D) :
    Qx2.Good k r 0 D (fun (f : Q.Mx k r → E) g => φ g • f g) := by
  refine ⟨fun f hf g₀ hg₀ => ?_, fun f f₂ h x hx => by simp only [h x hx], fun f f₂ s _ _ x _ => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
    exact ⟨U ∩ D, fun x => φ x • F x, hU.inter hD, ⟨hgU, hg₀.2⟩,
      (hφ.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hG => by
        simp only [he x hx.1 hG]⟩
  · simp only [smul_add, smul_comm s]

def mulE (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) (φ : Q.Mx k r → ℂ) :
    Module.End ℂ (levData E 0 hD).V :=
  (levData E 0 hD).hat (fun f g => φ g • f g)

theorem mulE_apply (hD : IsOpen D) {φ : Q.Mx k r → ℂ} (hφ : ContDiffOn ℝ ∞ φ D) (F : (levData E 0 hD).V)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r 0 ∩ D) :
    ((mulE E hD φ F : (levData E 0 hD).V) : Q.Mx k r → E) g = φ g • (F : Q.Mx k r → E) g := by
  unfold mulE
  rw [HatData.hat_apply (good0 hD (good_mul hD hφ))]
  exact level_restriction_apply_on _ hg

theorem end_ext (hD : IsOpen D) {X Y : Module.End ℂ (levData E 0 hD).V}
    (h : ∀ F, ∀ g ∈ Q.Glev k r 0 ∩ D, (X F : Q.Mx k r → E) g = (Y F : Q.Mx k r → E) g) : X = Y := by
  refine LinearMap.ext fun F => Subtype.ext ?_
  rw [← (X F).2.2, ← (Y F).2.2]
  exact (level_restriction_eq_iff _ _).2 (h F)

theorem mulE_pow_apply (hD : IsOpen D) {φ : Q.Mx k r → ℂ} (hφ : ContDiffOn ℝ ∞ φ D) (s : ℕ) (F : (levData E 0 hD).V)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r 0 ∩ D) :
    (((mulE E hD φ ^ s) F : (levData E 0 hD).V) : Q.Mx k r → E) g = φ g ^ s • (F : Q.Mx k r → E) g := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ', Module.End.mul_apply, mulE_apply hD hφ _ hg, ih, smul_smul, pow_succ']

theorem mulE_prod_apply (hD : IsOpen D) : ∀ {p : ℕ} (φ : Fin p → Q.Mx k r → ℂ) (_ : ∀ j, ContDiffOn ℝ ∞ (φ j) D)
    (F : (levData E 0 hD).V) {g : Q.Mx k r} (_ : g ∈ Q.Glev k r 0 ∩ D),
    (((List.ofFn fun j => mulE E hD (φ j)).prod F : (levData E 0 hD).V) : Q.Mx k r → E) g =
      (∏ j, φ j g) • (F : Q.Mx k r → E) g
  | 0, φ, _, F, g, _ => by simp
  | p + 1, φ, hφ, F, g, hg => by
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, mulE_apply hD (hφ 0) _ hg,
      mulE_prod_apply hD (fun j => φ j.succ) (fun j => hφ j.succ) F hg, smul_smul, Fin.prod_univ_succ]

def evAt (hD : IsOpen D) (F : (levData E 0 hD).V) (g : Q.Mx k r) : Module.End ℂ (levData E 0 hD).V →ₗ[ℂ] E where
  toFun := fun X => (X F : Q.Mx k r → E) g
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem evAt_apply (hD : IsOpen D) (F : (levData E 0 hD).V) (g : Q.Mx k r) (X : Module.End ℂ (levData E 0 hD).V) :
    evAt hD F g X = (X F : Q.Mx k r → E) g := rfl

end mul

section group

variable {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ)

theorem dim_eq (k r : ℕ) : r + 1 + (r + k) = Q.mdim k r 0 := by
  simp only [Q.mdim, Fin.val_zero]; omega

def pos (k r : ℕ) : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1) := finCongr (by omega)

theorem posL_cast (d : Fin (r + 1 + (r + k))) : Q.posL k r 0 (Fin.cast (dim_eq k r) d) = pos k r d := by
  apply Fin.ext; simp [Q.posL, pos]

def dZ (g : Q.Mx k r) : ℂ := (Zhat k r z z' g).det

def lam (g : Q.Mx k r) : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1)) ℂ :=
  fun a i => herm (Hpk k r) (g.mulVec (bvec (pos k r a))) (fvec k r z i)

theorem dZ_poly : U.IsPolyDeg (r + 1) (dZ z z') :=
  PartialDerivativeAlgebra.pd_det _ fun a b => zhat_pd k r z z' a b

theorem cramer_poly (a : Fin (r + 1 + (r + k))) (j : Fin (r + 1)) :
    U.IsPolyDeg (r + 1) (fun g => (Zhat k r z z' g).cramer (lam z g a) j) := by
  simp only [Matrix.cramer_apply]
  refine PartialDerivativeAlgebra.pd_det _ fun p q => ?_
  simp only [Matrix.updateCol_apply]
  split_ifs
  · exact _root_.PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_herm _ _ _
  · exact zhat_pd k r z z' p q

theorem isOpen_dom : IsOpen {g : Q.Mx k r | dZ z z' g ≠ 0} :=
  isOpen_ne_fun (contDiff_of_poly (dZ_poly z z')).continuous continuous_const

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def unitE (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : Fin (r + 1 + (r + k))) :
    Module.End ℂ (levData E 0 (isOpen_dom z z')).V :=
  E0 E 0 (isOpen_dom z z') (Fin.cast (dim_eq k r) a) (Fin.cast (dim_eq k r) b)

theorem row_mul_det (q : Fin (r + 1 + (r + k)) → ℂ) (a : Fin (r + 1 + (r + k)))
    (F : (levData E 0 (isOpen_dom z z')).V) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r 0 ∩ {g | dZ z z' g ≠ 0}) :
    evAt (isOpen_dom z z') F g ((∑ d, q d • unitE z z' E a d) * mulE E (isOpen_dom z z') (dZ z z')) =
      dZ z z' g • evAt (isOpen_dom z z') F g (∑ d, q d • unitE z z' E a d) +
        (∑ j : Fin (r + 1), (∑ d, q d * fvec k r z' j (pos k r d)) * (Zhat k r z z' g).cramer (lam z g a) j) •
          (F : Q.Mx k r → E) g := by
  have hs : ContDiffOn ℝ ∞ (dZ z z') {g | dZ z z' g ≠ 0} := (contDiff_of_poly (dZ_poly z z')).contDiffOn
  have key : ∀ d, evAt (isOpen_dom z z') F g (unitE z z' E a d * mulE E (isOpen_dom z z') (dZ z z')) =
      dZ z z' g • evAt (isOpen_dom z z') F g (unitE z z' E a d) +
        (∑ j : Fin (r + 1), fvec k r z' j (pos k r d) * (Zhat k r z z' g).cramer (lam z g a) j) •
          (F : Q.Mx k r → E) g := by
    intro d
    rw [evAt_apply, evAt_apply, Module.End.mul_apply, unitE, level_generator_apply _ _ _ _ hg, level_generator_apply _ _ _ _ hg,
      (Qx2.good_eh (isOpen_dom z z') _ _).loc _ (fun x => (Zhat k r z z' x).det • (F : Q.Mx k r → E) x)
        (fun x hx => mulE_apply _ hs F hx) g hg,
      _root_.GlobalTheory.HatNF.DetLeibniz.det_leibniz E k r z z' _ _ _ _ F.2.1 g hg]
    simp only [posL_cast]
    rfl
  rw [Finset.sum_mul]

  simp only [smul_mul_assoc, map_sum, map_smul, key, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun d _ => smul_comm _ _ _
  · simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

def coef (Qm : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ)
    (i : (Fin (r + k) → Fin (r + 1 + (r + k))) × (Fin (r + k) → Fin (r + 1 + (r + k)))) (g : Q.Mx k r) : ℂ :=
  Qm.det⁻¹ * ((Matrix.of fun a : Fin (r + 1 + (r + k)) =>
    Fin.append (lam z g a) (fun l : Fin (r + k) => if a = i.1 l then (1 : ℂ) else 0)).det *
      ((∏ l, Qm (Fin.natAdd (r + 1) l) (i.2 l)) * (((r + k).factorial : ℕ) : ℂ)⁻¹))

theorem coef_poly (Qm : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ) (i) :
    U.IsPolyDeg (r + 1 + (r + k)) (coef z Qm i) := by
  have h : U.IsPolyDeg (r + 1 + (r + k)) (fun g : Q.Mx k r => (Matrix.of fun a : Fin (r + 1 + (r + k)) =>
      Fin.append (lam z g a) (fun l : Fin (r + k) => if a = i.1 l then (1 : ℂ) else 0)).det) := by
    refine PartialDerivativeAlgebra.pd_det _ fun a b => ?_
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · simp only [Matrix.of_apply, Fin.append_left]
      exact _root_.PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_herm _ _ _
    · simp only [Matrix.of_apply, Fin.append_right]
      exact PartialDerivativeAlgebra.pd_const _ _
  exact PartialDerivativeAlgebra.pd_mono (by omega) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) (PartialDerivativeAlgebra.pd_mul h (PartialDerivativeAlgebra.pd_const _ 0)))

theorem group_identity (hz' : inWb k r z') (hT : 0 < Tz k r z') (Y : ℂ) :
    ∃ (Qm : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ) (w : ℂ),
      ∀ (F : Q.Mx k r → E), B.CkOn ⊤ (B.GV k r) F → ∀ g ∈ B.GV k r, dZ z z' g ≠ 0 →
      ∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
          (dZ z z' g ^ (r + 1 - (s : ℕ)) • Q.CV k r Y (fun x => dZ z z' x ^ (s : ℕ) • F x) g) =
        dZ z z' g ^ r • ∑ i : (Fin (r + k) → Fin (r + 1 + (r + k))) × (Fin (r + k) → Fin (r + 1 + (r + k))),
          coef z Qm i g • qminorOp (EabH (Hpk k r)) (pos k r ∘ i.1) (pos k r ∘ i.2) w F g := by
  obtain ⟨Qm, hQ, hQ1, hQ2⟩ := _root_.GlobalTheory.HatNF.DualFrame.exists_dual_matrix k r z' (pos k r) hz' hT
  set u := Q.uC k r 0 Y with hu
  refine ⟨Qm, u - ((r + 1 : ℕ) : ℂ), fun F hF g hgG hg0 => ?_⟩
  have hD := isOpen_dom z z'
  have hg : g ∈ Q.Glev k r 0 ∩ {g | dZ z z' g ≠ 0} := ⟨⟨hgG, fun a ha => absurd ha (by simp)⟩, hg0⟩
  have hFs : Q.SmoothLev k r 0 {g | dZ z z' g ≠ 0} F := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hF', he⟩ := hF g₀ hg₀.1.1
    exact ⟨U, F', hU, hgU, hF', fun x hx hG => he x hx hG.1⟩
  have hs : ContDiffOn ℝ ∞ (dZ z z') {g | dZ z z' g ≠ 0} := (contDiff_of_poly (dZ_poly z z')).contDiffOn
  set ν : Fin (r + 1 + (r + k)) → Fin (r + 1) → Q.Mx k r → ℂ :=
    fun a j x => (dZ z z' x)⁻¹ * (Zhat k r z z' x).cramer (lam z x a) j with hν
  have hνs : ∀ a j, ContDiffOn ℝ ∞ (ν a j) {g | dZ z z' g ≠ 0} := fun a j =>
    (hs.inv fun x hx => hx).mul (contDiff_of_poly (cramer_poly z z' a j)).contDiffOn
  have hGl : GlRel (unitE z z' E) := glRel_cast (dim_eq k r) (level_generators_gl_relations generator_gl_level 0 (isOpen_dom z z'))
  have top := _root_.GlobalTheory.CapelliTop.top_coefficient _ (r + 1) (r + k) (unitE z z' E) Qm (mulE E (isOpen_dom z z') (dZ z z'))
    (fun a j => mulE E (isOpen_dom z z') (ν a j)) u hGl
    (fun a j => end_ext _ fun G x hx => by
      have h := row_mul_det z z' (fun d => Qm (Fin.castAdd (r + k) j) d) a G hx
      rw [evAt_apply] at h
      rw [h, Module.End.mul_apply, mulE_apply _ hs _ hx, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
        mulE_apply _ (hνs a j) _ hx, smul_add, smul_smul]
      simp only [hQ1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hν]
      rw [mul_inv_cancel_left₀ hx.2]
      rfl)
    (fun a j => end_ext _ fun G x hx => by
      have h := row_mul_det z z' (fun d => Qm (Fin.natAdd (r + 1) j) d) a G hx
      rw [evAt_apply] at h
      rw [h, Module.End.mul_apply, mulE_apply _ hs _ hx]
      simp only [hQ2, zero_mul, Finset.sum_const_zero, zero_smul, add_zero]
      rfl)
    (fun a j => end_ext _ fun G x hx => by
      rw [Module.End.mul_apply, Module.End.mul_apply, mulE_apply _ hs _ hx, mulE_apply _ (hνs a j) _ hx,
        mulE_apply _ (hνs a j) _ hx, mulE_apply _ hs _ hx, smul_comm])
  have mnr := _root_.GlobalTheory.ScalarColsMinor.antisym_prod_eq_sum_qminor _ (r + 1) (r + k) (unitE z z' E) (fun l d => Qm (Fin.natAdd (r + 1) l) d) (lam z g)
    ((Zhat k r z z' g)⁻¹).transpose (u - ((r + 1 : ℕ) : ℂ))
  set F0 := (levData E 0 (isOpen_dom z z')).toV F hFs with hF0
  have hF0v : ∀ x ∈ Q.Glev k r 0 ∩ {g | dZ z z' g ≠ 0}, (F0 : Q.Mx k r → E) x = F x := fun x hx => level_restriction_apply_on F hx
  have e1 := congrArg (evAt (isOpen_dom z z') F0 g) top
  have e2 := congrArg (evAt (isOpen_dom z z') F0 g) mnr
  have hU : IsUnit (Zhat k r z z' g).det := isUnit_iff_ne_zero.2 hg0
  have hLN : ∀ a j, (lam z g * ((Zhat k r z z' g)⁻¹).transpose) a j = ν a j g := by
    intro a j
    have := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer (Zhat k r z z' g) (lam z g a) hU) j
    simp only [hν]
    rw [← this, Pi.smul_apply, smul_eq_mul, dZ, inv_mul_cancel_left₀ hU.ne_zero]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hL : ∀ s : ℕ, ∀ t : ℕ, evAt (isOpen_dom z z') F0 g (mulE E (isOpen_dom z z') (dZ z z') ^ t *
      (qdet (unitE z z' E) u * mulE E (isOpen_dom z z') (dZ z z') ^ s)) =
      dZ z z' g ^ t • Q.CV k r Y (fun x => dZ z z' x ^ s • F x) g := by
    intro s t
    rw [evAt_apply, Module.End.mul_apply, mulE_pow_apply _ hs _ _ hg, Module.End.mul_apply]
    congr 1
    have : qdet (unitE z z' E) u = qminor (E0 E 0 (isOpen_dom z z')) id id u := qdet_cast (dim_eq k r) _ u
    rw [this, quantum_minor_level_apply _ _ _ _ _ hg]
    exact (Qx2.good_qminor (isOpen_dom z z') id id u).loc _ _
      (fun x hx => by rw [mulE_pow_apply _ hs _ _ hx, hF0v x hx]) g hg
  have hR : ∀ c d : Fin (r + k) → Fin (r + 1 + (r + k)), ∀ w : ℂ,
      evAt (isOpen_dom z z') F0 g (qminor (unitE z z' E) c d w) =
        qminorOp (EabH (Hpk k r)) (pos k r ∘ c) (pos k r ∘ d) w F g := by
    intro c d w
    have : qminor (unitE z z' E) c d w = qminor (E0 E 0 (isOpen_dom z z')) (Fin.cast (dim_eq k r) ∘ c)
      (Fin.cast (dim_eq k r) ∘ d) w := qminor_cast' (dim_eq k r) _ c d w
    rw [evAt_apply, this, quantum_minor_level_apply _ _ _ _ _ hg,
      (Qx2.good_qminor (isOpen_dom z z') _ _ w).loc _ _ hF0v g hg]
    have hc : ∀ c : Fin (r + k) → Fin (r + 1 + (r + k)),
        Q.posL k r 0 ∘ Fin.cast (dim_eq k r) ∘ c = pos k r ∘ c := fun c => funext fun l => posL_cast _
    rw [hc, hc]
  have hM : ∀ (σ : Equiv.Perm (Fin (r + 1 + (r + k)))) (X : Module.End ℂ (levData E 0 (isOpen_dom z z')).V),
      evAt (isOpen_dom z z') F0 g ((List.ofFn fun j : Fin (r + 1) =>
        mulE E (isOpen_dom z z') (ν (σ (Fin.castAdd (r + k) j)) j)).prod * X) =
      (∏ j : Fin (r + 1), ν (σ (Fin.castAdd (r + k) j)) j g) • evAt (isOpen_dom z z') F0 g X := by
    intro σ X
    rw [evAt_apply, Module.End.mul_apply, mulE_prod_apply _ _ (fun j => hνs _ j) _ hg]
    rfl
  have hP : ∀ X : Module.End ℂ (levData E 0 (isOpen_dom z z')).V,
      evAt (isOpen_dom z z') F0 g (mulE E (isOpen_dom z z') (dZ z z') ^ (r + 1) * X) =
        dZ z z' g ^ (r + 1) • evAt (isOpen_dom z z') F0 g X := by
    intro X
    rw [evAt_apply, Module.End.mul_apply, mulE_pow_apply _ hs _ _ hg]
    rfl
  rw [hP] at e1

  simp only [map_smul, map_sum, hL, hM, hR, hLN] at e1 e2
  simp only [mul_smul] at e2
  rw [e2, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at e1
  rw [Fintype.sum_prod_type]
  simp only [coef, mul_smul, ← Finset.smul_sum]
  rw [eq_comm, ← inv_smul_eq_iff₀ hQ] at e1
  rw [← e1, smul_smul, smul_smul, smul_smul]
  congr 1
  have h0 : (Zhat k r z z' g).det ≠ 0 := hg0
  unfold dZ
  field_simp
  ring

end group

section radial

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem dZ_eq {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) :
    dZ z z' g = Dmin k r z z' g (Fin.last (r + 1)) := by
  unfold dZ Dmin
  congr 1

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem cpt_mul {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ∞ φ) : KB.CptCoef Bs (fun g => φ g • F g) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  refine ⟨fun g₀ hg₀ => ?_, ⟨R, fun g hg h => hR g hg fun h0 => h (by simp [h0])⟩,
    ⟨ε, hε, fun g hg h => hG g hg fun h0 => h (by simp [h0])⟩⟩
  obtain ⟨U, F', hU, hgU, hF', he⟩ := hs g₀ hg₀
  exact ⟨U, fun x => φ x • F' x, hU, hgU, hφ.contDiffOn.smul hF', fun x hx hG => by simp only [he x hx hG]⟩

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem cpt_congr {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F F₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    (h : ∀ g ∈ B.GV k r, F₂ g = F g) : KB.CptCoef Bs F₂ := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  refine ⟨fun g₀ hg₀ => ?_, ⟨R, fun g hg h' => hR g hg (h g hg ▸ h')⟩,
    ⟨ε, hε, fun g hg h' => hG g hg (h g hg ▸ h')⟩⟩
  obtain ⟨U, F', hU, hgU, hF', he⟩ := hs g₀ hg₀
  exact ⟨U, F', hU, hgU, hF', fun x hx hG => by rw [h x hG, he x hx hG]⟩

omit [FiniteDimensional ℂ Wp] in
theorem cpt_cap {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    (Y : ℂ) : KB.CptCoef Bs (Q.CV k r Y F) := by
  obtain ⟨Lw, hLw, hCV⟩ := capelli_word_sum k r Y
  have hLie : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ Lw, cw.2.length ≤ 2 * r + k + 1 := fun cw h => (hLw cw h).2
  have hs : B.SmoothCoef (C6.domL Bs ∅) (TLB.capOp k r Wp Wq 1 Lw) := by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).1
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).1
  refine cpt_congr ((compact_support_facts k r Wp Wq Bs F hF).2 _ hs).1 fun g hg => ?_
  rw [TLB.opApply_capOp 1 Lw hLie, hCV _ _ F (B5.ckOn_mono le_top hF.1) g hg hg, one_smul]

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem jf_mul_det {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (s : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.JF Bs (fun x => dZ Bs.z Bs.z' x ^ s • F x) g = dZ Bs.z Bs.z' g ^ s • B.JF Bs F g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun x => dZ Bs.z Bs.z' x ^ s • F x) g ∂Bs.μSS =
    dZ Bs.z Bs.z' g ^ s • ∫ p, JF.xiP Bs p • B.rho Bs p F g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [B5.ae_inSS Bs] with p hp
  simp only [B.rho, dZ_eq]
  rw [BigCellZetaMinors.dmin_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem jf_sum {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {ι : Type} (s : Finset ι) (F : ι → B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : ∀ i, KB.CptCoef Bs (F i)) {g : B.Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    KB.CptCoef Bs (fun x => ∑ i ∈ s, F i x) ∧ B.JF Bs (fun x => ∑ i ∈ s, F i x) g = ∑ i ∈ s, B.JF Bs (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using PBN.cpt_zero' Bs, by simpa using JCx2.bc_JF_zero _⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine ⟨PBN.cpt_add Bs (hF a) ih.1, ?_⟩
    obtain ⟨ε₁, -, hn₁⟩ := TLB.nice_of_cpt (hF a)
    obtain ⟨ε₂, -, hn₂⟩ := TLB.nice_of_cpt ih.1
    rw [JCx2.bc_JF_add (TLB.nice_mono hn₁ (min_le_left ε₁ ε₂)) (TLB.nice_mono hn₂ (min_le_right ε₁ ε₂)) hg, ih.2]

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
  {μ : Measure (Mt P.k P.r)} {L : LevelData (RA P Bs) P.r} {st : Start (RA P Bs)} {l0 : ℕ}

theorem rad_cap (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (Y : ℂ)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) {Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    (hΦ : Top.IsRadOf P Bs Φ F) :
    Top.IsRadOf P Bs ((P5.QQi L st 0 Y 0 0).1 Φ) (fun g => M.sgn P l0 • Q.CV P.k P.r Y F g) := by
  intro y hy
  set s : ℂ := M.sgn P l0 with hs
  obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hL := hD.2.2.1
  have hst := hD.2.2.2.1
  have hJ := bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
  have hh := TLB.wCell_om Bs hy
  have h1 := JCx2.rma_QQi X L hL st s hst Y 0 0 Φ hy
  have hloc : ∀ n, n ≤ P.r → ∀ N : Q.OM (Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      JCx2.rma_Loc P.k P.r Bs.z Bs.z' N →
      JCx2.rma_Loc P.k P.r Bs.z Bs.z' (Q.sandw P.k P.r Y n N) := by
    intro n
    induction n with
    | zero =>
      intro _ N hN
      simpa only [Q.sandw] using hN
    | succ n ih =>
      intro hn N hN
      have h : n < P.r := by omega
      simp only [Q.sandw, dif_pos h]
      apply ih (by omega)
      intro a b f₁ f₂ he y' hy'
      simp only [Q.oMul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      refine JCx2.rma_TLs_loc ⟨n, h⟩ Y a c _ _ (fun y'' hy'' => ?_) y' hy'
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun d _ => ?_
      exact hN c d _ _ (JCx2.rma_TL_loc ⟨n, h⟩ Y d b f₁ f₂ he) y'' hy''
  have h2 := hloc P.r le_rfl _ (JCx2.rma_QL_loc Y) 0 0
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F)) (fun y' hy' => hΦ y' hy') y hy
  have h3 := chain_recursion_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) _ Y 0 0 hz hz'
    (JCx2.rma_isDom_omPlus hz hz') _ hJ y.1 hy.1 y.2 hy.2.1 hh.2
  rw [Fin.val_last] at h3
  have h4 : B.JF Bs (fun g => s • Q.CV P.k P.r Y F g) (Q.wCell P.k P.r (Fin.last P.r) y.1 * y.2) =
      s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 (B.JF Bs F) (Q.wCell P.k P.r (Fin.last P.r) y.1 * y.2) :=
    (JCx2.bcGood_tL (Bs := Bs) (ε := ε) s Y 0 0).2.1 F hN _ hh
  refine Eq.trans h1 ?_
  rw [h2, ← h3]
  simp only [Q.resG]
  rw [h4, smul_comm]

theorem mulAt_pow {x : (Fin P.r → ℂ) × Q.Mx P.k P.r} {a : RA P Bs} {s : ℂ} (h : TLB.MulAt x a.1 s) :
    ∀ n : ℕ, TLB.MulAt x (a ^ n).1 (s ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact TLB.mulAt_one x
  | n + 1 => by rw [pow_succ, pow_succ]; exact TLB.mulAt_mul (mulAt_pow h n) h

theorem act_fns (hL : Q.IsActualLevel X L) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') :
    TLB.MulAt x L.Dr.1 (∏ a, x.1 a) ∧ TLB.MulAt x L.ζi.1 (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ ∧
    TLB.MulAt x L.D.1 (dZ Bs.z Bs.z' (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)) ∧
    TLB.MulAt x L.Di.1 (dZ Bs.z Bs.z' (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2))⁻¹ := by
  have hcell := big_cell_values P.k P.r Wp Wq Bs x hx
  have hDr : TLB.MulAt x L.Dr.1 (∏ a, x.1 a) := TLB.mulAt_ofFn L.c _ fun l => TLB.act_c X L hL x l
  have hDri : TLB.MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹) := TLB.mulAt_ofFn L.ci _ fun l => TLB.act_ci X L hL x l
  have hz : TLB.MulAt x L.ζ.1 (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2) := by
    rw [hL.2.2.2.2.2.2.1]; exact TLB.act_fn X x hx 0
  have hzi : TLB.MulAt x L.ζi.1 (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ := by
    rw [hL.2.2.2.2.2.2.2.1]; exact TLB.act_fn X x hx 1
  refine ⟨hDr, hzi, ?_, ?_⟩
  · rw [dZ_eq, hcell.2.2.1]
    exact TLB.mulAt_mul hDr hz
  · rw [dZ_eq, hcell.2.2.1, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact TLB.mulAt_mul hzi hDri

theorem dZ_ne {g : B.Mat P.k P.r} (hg : g ∈ C6.domL Bs ∅) : dZ Bs.z Bs.z' g ≠ 0 := by
  intro h
  have := gram_function_last_minor P.k P.r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g _ le_rfl
  rw [← dZ_eq, h, map_zero] at this
  exact absurd hg.2.1 (not_lt.2 this)

theorem lift_regular {d : Q.NFData P (RA P Bs)} (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (hd : IsNF X d)
    (y : ℝ) (h1 : (y : ℂ) ∈ st.inv) (h2 : (y : ℂ) - 1 ∈ st.inv) :
    PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rhv d y) := by
  have hy : star (y : ℂ) = y := Complex.conj_ofReal y
  obtain ⟨hA, hC, -⟩ := actual_algebra_facts Wp Wq P _ _ _ _ X μ L st l0 hD
  have hB := (TL.bFromCap _ P.r L st hA y hy h1 (Or.inl h2)).2
  have hL := hD.2.2.1
  have hdL := hd.1
  obtain ⟨Qm, w, hG⟩ := group_identity (E := Wq →L[ℂ] Wp) Bs.z Bs.z' Bs.z'_mem Bs.T'_pos (y : ℂ)
  obtain ⟨Θ, hΘ, hap⟩ := _root_.GlobalTheory.HatNF.MinorPoly.minor_polyOp Wp Wq P.k P.r (P.r + P.k) (P.r + 1 + (P.r + P.k)) _
    (fun i : (Fin (P.r + P.k) → Fin (P.r + 1 + (P.r + P.k))) × (Fin (P.r + P.k) → Fin (P.r + 1 + (P.r + P.k))) =>
      pos P.k P.r ∘ i.1) (fun i => pos P.k P.r ∘ i.2) w (fun i g => -coef Bs.z Qm i g)
    (fun i => by
      have := PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const (-1) 0) (coef_poly Bs.z Qm i)
      simpa using this)
  refine ⟨Θ, fun T hT => ?_, fun F hF Φ hΦ x hx => ?_⟩
  · obtain ⟨hl, φ, hφ, hc⟩ := hΘ T hT
    exact ⟨by omega, φ, PartialDerivativeAlgebra.pd_mono (by nlinarith) hφ, hc⟩
  have hT : L.Tvprod y = d.L.Tvprod y := by
    unfold LevelData.Tvprod
    congr 3
    funext l
    unfold LevelData.Tvl
    rw [hL.2.1 l, hdL.2.1 l, hL.2.2.2.2.1 l, hdL.2.2.2.2.1 l, hL.2.2.2.2.2.1 l, hdL.2.2.2.2.2.1 l]
  set s : ℂ := M.sgn P l0 with hs
  have hss : s * s = 1 := by rw [hs, M.sgn, ← mul_pow]; simp
  set W : RA P Bs := d.QQ y 0 1 * d.L.Avr y + d.QQ y 1 1 * d.L.Bvr y with hW
  have hbM : TL.bM L st y = L.ζi * (s • W) := by
    unfold TL.bM
    rw [hD.2.2.2.1, hd.2.2.2, hW]
    simp only [Matrix.smul_apply, smul_add, smul_mul_assoc, LevelData.Avr, LevelData.Bvr, hT]
    rfl
  set h := Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 with hh
  have hdom : h ∈ C6.domL Bs ∅ := PBN.cell_dom Bs hx
  have hD0 := dZ_ne hdom
  have hcell := (big_cell_values P.k P.r Wp Wq Bs x hx).2.2.1
  rw [← dZ_eq] at hcell
  have hζ : Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 ≠ 0 := fun h0 => hD0 (by rw [hh, hcell, h0, mul_zero])
  have hφ : ∀ t : ℕ, ContDiff ℝ ∞ fun g => dZ Bs.z Bs.z' g ^ t := fun t =>
    (contDiff_of_poly (dZ_poly Bs.z Bs.z')).pow t
  have e1 : ((rhv d y).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (s * dZ Bs.z Bs.z' h) • ((TL.bM L st y).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    have a1 := (act_fns hdL hx).1 (W.1 Φ)
    have a2 := (act_fns hL hx).2.1 ((s • W).1 Φ)
    have a3 : ((s • W).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = s • (W.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 :=
      rfl
    rw [hbM]
    refine a1.trans (Eq.symm ((congrArg _ a2).trans ?_))
    rw [a3, smul_smul, smul_smul, hh, hcell]
    congr 1
    calc _ = s * s * (∏ a, x.1 a) * (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 *
        (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹) := by ring
      _ = _ := by rw [hss, mul_inv_cancel₀ hζ, one_mul, mul_one]
  have e2 : ∀ t : ℕ, ((L.Di ^ t * TL.cst L st y * L.D ^ t).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (dZ Bs.z Bs.z' h)⁻¹ ^ t • s •
        Q.resG P.k P.r (Fin.last P.r) (B.JF Bs (Q.CV P.k P.r y fun g => dZ Bs.z Bs.z' g ^ t • F g)) x.1 x.2 := by
    intro t
    have r1 : Top.IsRadOf P Bs ((L.D ^ t).1 Φ) (fun g => dZ Bs.z Bs.z' g ^ t • F g) := by
      intro x' hx'
      rw [mulAt_pow (act_fns hL hx').2.2.1 t Φ, hΦ x' hx']
      simp only [Q.resG]
      rw [jf_mul_det, smul_comm]
    have r2 := rad_cap hD y (cpt_mul hF (hφ t)) r1 x hx
    rw [hC y hy] at r2
    refine (mulAt_pow (act_fns hL hx).2.2.2 t ((TL.cst L st y).1 ((L.D ^ t).1 Φ))).trans ?_
    rw [r2]
    simp only [Q.resG]
    rw [JCx2.bc_JF_smul, smul_comm s]
  have e3 : ((TL.bM L st y).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      -∑ t : Fin (P.r + 2), ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) t : ℝ) : ℂ) •
        ((L.Di ^ (t : ℕ) * TL.cst L st y * L.D ^ (t : ℕ)).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    let ev : RA P Bs →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
      { toFun := fun a => (a.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have := congrArg ev hB

    rw [map_neg, map_sum] at this
    simp only [map_smul] at this
    exact this
  have e4 : dZ Bs.z Bs.z' h ^ P.r • B.JF Bs (B.opApply Θ F) h =
      -∑ t : Fin (P.r + 2), ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) t : ℝ) : ℂ) •
        (dZ Bs.z Bs.z' h ^ (P.r + 1 - (t : ℕ)) •
          B.JF Bs (Q.CV P.k P.r y fun g => dZ Bs.z Bs.z' g ^ (t : ℕ) • F g) h) := by
    have hj := (jf_sum Bs Finset.univ (fun (t : Fin (P.r + 2)) g =>
      ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) t : ℝ) : ℂ) • (dZ Bs.z Bs.z' g ^ (P.r + 1 - (t : ℕ)) •
        Q.CV P.k P.r y (fun g => dZ Bs.z Bs.z' g ^ (t : ℕ) • F g) g))
      (fun t => PBN.cpt_smul Bs _ (cpt_mul (cpt_cap (cpt_mul hF (hφ t)) y) (hφ _))) (TLB.wCell_om Bs hx)).2
    simp only [JCx2.bc_JF_smul, jf_mul_det] at hj
    rw [← hj, ← jf_mul_det, ← neg_one_smul ℂ, ← JCx2.bc_JF_smul]
    refine PBN.jf_congr_pos Bs (fun g hg => ?_) hdom
    rw [hG F hF.1 g hg.1 (dZ_ne hg), hap F g hg.1 Set.univ isOpen_univ trivial (by rw [Set.inter_univ]; exact hF.1)]
    simp only [neg_smul, Finset.sum_neg_distrib, smul_neg, one_smul]
  rw [e1, e3]
  simp only [e2, Q.resG]
  rw [← hh, ← inv_smul_smul₀ (pow_ne_zero P.r hD0) (B.JF Bs (B.opApply Θ F) h), e4]
  simp only [smul_neg, Finset.smul_sum, smul_smul, neg_inj]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have ht : (t : ℕ) ≤ P.r + 1 := Nat.lt_succ_iff.1 t.isLt
  rw [pow_sub₀ _ hD0 ht, inv_pow, pow_succ]
  field_simp
  rw [pow_two, hss, one_mul]

end radial

theorem polyLift_rhv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rhv d y) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hd y
  let K : Submodule ℂ (RA P Bs) :=
    { carrier := {a | PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) a}
      zero_mem' := ⟨[], fun T hT => by simp at hT, TLB.radIs_zero P Bs⟩
      add_mem' := by
        rintro a b ⟨Θ₁, h₁, r₁⟩ ⟨Θ₂, h₂, r₂⟩
        refine ⟨Θ₁ ++ Θ₂, fun T hT => ?_, TLB.radIs_add P Bs ((polyOp_ok _ _ _ _ _ _ _ h₁).1 _)
          ((polyOp_ok _ _ _ _ _ _ _ h₂).1 _) r₁ r₂⟩
        rcases List.mem_append.1 hT with h | h
        · exact h₁ T h
        · exact h₂ T h
      smul_mem' := by
        rintro c a ⟨Θ, h, r⟩
        refine ⟨Θ.map (TLB.smulT c), fun T hT => ?_, TLB.radIs_smul P Bs c r⟩
        obtain ⟨T₀, h₀, rfl⟩ := List.mem_map.1 hT
        obtain ⟨hl, φ, hφ, hc, hc'⟩ := h T₀ h₀
        refine ⟨hl, fun g => c * φ g, by simpa using PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const c 0) hφ, fun g => ?_, fun g => ?_⟩
        · show c • T₀.coef g = _
          rw [hc, smul_smul]
        · show (starRingEnd ℂ) c • T₀.coefAdj g = _
          rw [hc', smul_smul, star_mul']
          rfl }
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ (ρ : M.Ty P) (i : Finset.Icc 1 (P.k - 1)), -(M.rho P ρ i : ℝ) ≤ b := by
    obtain ⟨b, hb⟩ := (Set.finite_range fun x : M.Ty P × Finset.Icc 1 (P.k - 1) => -(M.rho P x.1 x.2 : ℝ)).bddAbove
    exact ⟨b, fun ρ i => hb ⟨(ρ, i), rfl⟩⟩
  have hinv : ∀ t : ℝ, b < t → (t : ℂ) ∈ st.inv := by
    intro t ht
    rw [hD.2.2.2.2.2.1]
    intro ρ
    unfold M.xC
    refine Finset.prod_ne_zero_iff.2 fun i hi h0 => ?_
    have h1 := hb ρ ⟨i, hi⟩
    have h2 : t + M.rho P ρ i = 0 := by exact_mod_cast h0
    simp only at h1
    linarith
  refine _root_.GlobalTheory.RhvPoly.rhv_mem_of_infinite P _ d K ((fun t : ℝ => (t : ℂ)) '' Set.Ioi (b + 1))
    ((Set.Ioi_infinite _).image Complex.ofReal_injective.injOn) ?_ y
  rintro _ ⟨t, ht, rfl⟩
  have ht' : b + 1 < t := ht
  refine lift_regular hD hd t (hinv t (by linarith)) ?_
  have := hinv (t - 1) (by linarith)
  rwa [Complex.ofReal_sub, Complex.ofReal_one] at this

end

end GlobalTheory.HatNF.MirrorLift
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombination =====
