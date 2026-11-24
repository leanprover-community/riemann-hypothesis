module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne

variable {q : ℕ} [Fact q.Prime] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def IsMom (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (μ : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) : Prop :=
  ∀ (k : ℕ) (j : Fin k → κ) (f : C(κ → ℤ_[q], ℂ_[q])), (∀ a, f a = ∏ l, zc (a (j l))) →
    ι (iteratedFDeriv ℂ k G 0 fun l => v (j l)) = μ f

def MomInt (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) : Prop :=
  ∃ μ : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], ‖μ‖ ≤ 1 ∧ IsMom ι v G μ

def LatInt (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) (G : V → ℂ) : Prop :=
  ∀ (κ : Type) [Fintype κ] (v : κ → V), (∀ i, v i ∈ Λ) → MomInt ι (fun i => ι.symm ω • v i) G

def monoJet {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (m : κ →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ m.toMultiset.toList.length G 0 fun l => v (m.toMultiset.toList.get l)

def mahler {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (n : κ → ℕ) : ℂ :=
  let P : MvPolynomial κ ℂ :=
    ∏ i, MvPolynomial.C (((n i).factorial : ℂ)⁻¹) * Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ (n i))
  ∑ m ∈ P.support, P.coeff m * monoJet v G m

def Per (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) : Prop :=
  IsTh d θ ∧ δ₀ ^ 12 = discr d ∧ δ₀ ≠ 0 ∧
  (∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' d (Ω' / ι' δ₀) θ) ∧
  ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ₀) θ ∧ ∃ M : Mdl q, M.ι = ι ∧ IsOK d M.L ∧ M.MChart (Ω / ι δ₀)

theorem latInt_zero (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) : LatInt ι ω Λ (fun _ => 0) := by
  intro κ _ v _
  refine ⟨0, by simp, ?_⟩
  intro k j f _
  simp

theorem latInt_one (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) : LatInt ι ω Λ (fun _ => 1) := by
  intro κ _ v _
  refine ⟨ContinuousMap.evalCLM ℂ_[q] 0, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul]
    exact f.norm_coe_le_norm 0
  · intro k j f hf
    rw [ContinuousMap.evalCLM_apply, hf]
    cases k with
    | zero => simp
    | succ k =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k), Finset.prod_eq_zero (Finset.mem_univ 0)]
      · simp
      · simp [zc]

end GlobalTheory.MomN
