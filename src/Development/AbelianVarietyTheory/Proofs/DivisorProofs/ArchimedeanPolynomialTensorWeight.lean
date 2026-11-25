module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

noncomputable section
namespace GlobalTheory.FockKStab
open GlobalTheory.ExpAct
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem mem_of_exp {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (hL : LocFin L) (N : Submodule ℂ V)
    (T : V) (h : ∀ s : ℝ, ∃ U : Module.End ℂ V, IsExp ((s : ℂ) • L) U ∧ U T ∈ N) : L T ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  set l : V →ₗ[ℂ] ℂ := l' ∘ₗ N.mkQ with hldef
  have hl : ∀ v ∈ N, l v = 0 := fun v hv => by simp [hldef, (Submodule.Quotient.mk_eq_zero N).2 hv]
  show l (L T) = 0
  obtain ⟨N0, hfin, hT, hN0⟩ := hL T
  set A := mat L N0 hN0
  set x := crd N0 ⟨T, hT⟩
  set φ := l ∘ₗ emb N0
  have hpow : ∀ n : ℕ, φ ((A ^ n) *ᵥ x) = l ((L ^ n) T) := fun n => by
    simp only [φ, LinearMap.comp_apply, A, emb_pow_mulVec, x, emb_crd]
  have hg : ∀ s : ℝ, φ (NormedSpace.exp (s • A) *ᵥ x) = 0 := by
    intro s
    obtain ⟨U, hU, hUN⟩ := h s
    have h1 := hU T l
    have h2 := hasSum_exp_mulVec (s • A) φ x
    have e : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ * φ (((s • A) ^ n) *ᵥ x) =
        ((n.factorial : ℂ))⁻¹ * l ((((s : ℂ) • L) ^ n) T) := fun n => by
      rw [smul_pow, smul_pow, Matrix.smul_mulVec, LinearMap.map_smul_of_tower, hpow, LinearMap.smul_apply,
        map_smul]
      simp [Complex.real_smul]
    simp only [e] at h2
    rw [h2.unique h1, hl _ hUN]
  let ψ : Matrix (Fin (Module.finrank ℂ N0)) (Fin (Module.finrank ℂ N0)) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => φ (M *ᵥ x)
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun r M => by
        rw [Matrix.smul_mulVec, LinearMap.map_smul_of_tower]; rfl }
  have hd : HasDerivAt (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A)))
      (ψ.toContinuousLinearMap (A * NormedSpace.exp ((0 : ℝ) • A))) 0 :=
    (ψ.toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const' A (0 : ℝ))
  have hz : (fun u : ℝ => ψ.toContinuousLinearMap (NormedSpace.exp (u • A))) = fun _ => 0 := by
    funext u; exact hg u
  rw [hz] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  simp only [zero_smul, NormedSpace.exp_zero, mul_one] at this
  have e2 : ψ.toContinuousLinearMap A = l (L T) := by
    show φ (A *ᵥ x) = _
    simp only [φ, LinearMap.comp_apply, A, emb_mulVec, x, emb_crd]
  rw [← e2]; exact this

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

theorem jm_mul_jm (R S : ℕ) : Formalism.BasicNotions.TH.Jm R S * Formalism.BasicNotions.TH.Jm R S = 1 := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem commute_jm {R S : ℕ} {X : Mat R S} (hX : IsKC X) : Commute X (Formalism.BasicNotions.TH.Jm R S) := by
  show X * _ = _ * X
  have h1 : ∀ i j, X (Sum.inl i) (Sum.inr j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  have h2 : ∀ i j, X (Sum.inr i) (Sum.inl j) = 0 := fun i j => hX _ _ (by simp [sameBlock])
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply, h1, h2]

theorem isKC_smul {R S : ℕ} {X : Mat R S} (hX : IsKC X) (c : ℂ) : IsKC (c • X) := fun a b h => by
  simp [hX a b h]

theorem isKC_zero (R S : ℕ) : IsKC (0 : Mat R S) := fun a b _ => rfl

theorem isKC_add {R S : ℕ} {X X' : Mat R S} (hX : IsKC X) (hX' : IsKC X') : IsKC (X + X') := fun a b h => by
  simp [hX a b h, hX' a b h]

theorem isKC_conjTranspose {R S : ℕ} {X : Mat R S} (hX : IsKC X) : IsKC Xᴴ := fun a b h => by
  have h' : ¬ sameBlock b a := by
    intro h2; apply h; rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  simp [Matrix.conjTranspose_apply, hX b a h']

theorem mem_upq {R S : ℕ} {X : Mat R S} (hX : IsKC X) (hs : Xᴴ = -X) : X ∈ upq R S := by
  show Xᴴ * _ + _ * X = 0
  rw [hs, ← (commute_jm hX).eq]; simp

theorem frame_inv {α : Type} [Fintype α] [DecidableEq α] {R S : ℕ} {M : Matrix α α ℂ} {C : Matrix α (Ix R S) ℂ}
    {A' : Matrix (Ix R S) α ℂ} (h : IsFrame M C) (hA : C * A' = 1) : A' * C = 1 := by
  set K := M * C.map star * Formalism.BasicNotions.TH.Jm R S
  have h1 : Cᵀ * K = 1 := by
    simp only [K, ← Matrix.mul_assoc, h.1, jm_mul_jm]
  have h2 : Kᵀ * C = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : A' = Kᵀ := by
    calc A' = (Kᵀ * C) * A' := by rw [h2, Matrix.one_mul]
      _ = Kᵀ := by rw [Matrix.mul_assoc, hA, Matrix.mul_one]
  rw [h3, h2]

theorem commute_of_frame {α : Type} [Fintype α] [DecidableEq α] {R S : ℕ} {C : Matrix α (Ix R S) ℂ}
    {A' : Matrix (Ix R S) α ℂ} (hCA : C * A' = 1) (hAC : A' * C = 1) {G θ : Matrix α α ℂ} {E : Mat R S}
    (hG : G * C = C * E) (hθ : θ * C = C * Formalism.BasicNotions.TH.Jm R S) (hE : Commute E (Formalism.BasicNotions.TH.Jm R S)) : Commute G θ := by
  have hG' : G = C * E * A' := by rw [← hG, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hθ' : A' * θ = Formalism.BasicNotions.TH.Jm R S * A' := by
    calc A' * θ = A' * θ * (C * A') := by rw [hCA, Matrix.mul_one]
      _ = A' * (θ * C) * A' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hθ]; simp only [← Matrix.mul_assoc, hAC, Matrix.one_mul]
  show G * θ = θ * G
  rw [hG']
  calc C * E * A' * θ = C * E * (A' * θ) := by rw [Matrix.mul_assoc]
    _ = C * (E * Formalism.BasicNotions.TH.Jm R S) * A' := by rw [hθ']; simp only [Matrix.mul_assoc]
    _ = (θ * C) * E * A' := by rw [hE.eq, hθ]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.FockKStab
end

noncomputable section
namespace GlobalTheory.FockKStab
open Matrix

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

end Tensor





end GlobalTheory.FockKStab
end
