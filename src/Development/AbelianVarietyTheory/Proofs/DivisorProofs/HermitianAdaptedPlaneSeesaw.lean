module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXEvUniq

open scoped Classical

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
  {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem schr_add [Invertible (2 : R)] (ψ : AddChar R ℂ) (a b : (α → R) × (α → R)) (h : a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (φ : (α → R) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x, ← h]
  congr 2
  have h2 : (⅟(2 : R)) * 2 = 1 := invOf_mul_self _
  linear_combination (a.1 ⬝ᵥ b.2) * h2

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_smul {α β : Type} (a : F) (A : Matrix α β E) : incM F (a • A) = algebraMap F (AF F) a • incM F A := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, algebraMap_smul]
  exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) a _

def emb (F : Type) [Field F] [NumberField F] {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))

variable {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d}

abbrev colM {S : Type} {n : ℕ} (x : Fin n → S) : Matrix (Fin n) Unit S := Matrix.replicateCol Unit x

abbrev sp (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) :
    Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)

end GlobalTheory.MixXEvUniq

end
