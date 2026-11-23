module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Decomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SiegelDiagDecomp
open Matrix

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {β : Type} [Fintype β] [DecidableEq β]

theorem diag_decomp : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (β : Type) [Fintype β] [DecidableEq β]
    (J : Matrix β β A), IsUnit J.det → ∀ e : R, e * e = e → ∀ g k : UG c J,
    (1 - e) • ((g.1.1 : Matrix β β A) - 1) = 0 → (1 - e) • ((k.1.1 : Matrix β β A) - 1) = 0 →
    ∀ a b : Matrix β β A, e • a = a → e • b = b →
    a * (1 - (k.1.1 : Matrix β β A)) = e • (1 : Matrix β β A) → (1 - (k.1.1 : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) = e • (1 : Matrix β β A) →
    (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ gd kd : UG c (dbl J), (gd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (g.1.1 : Matrix β β A) 0 0 1 →
    (kd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (k.1.1 : Matrix β β A) 0 0 1 →
    ∃ (p₁ p₂ : UG c (dbl J)) (t₁ t₂ : GL β A), (1 - e) • ((p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (1 - e) • ((p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₁.val ∧
      (p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₂.val ∧ gd = kd * p₁ * kd⁻¹ * p₂ := by
  first
  | exact @_root_.GlobalTheory.UnipotentCongruenceInverse.decomposition
  | exact _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition
  | (apply _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentCongruenceInverse.decomposition <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition ..)

end GlobalTheory.SiegelDiagDecomp
