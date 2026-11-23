module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qO_extTensor_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : MirUin k (i + 1)) (hu : mirChar k ψ i u = 1) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1) v) = qO τ σ ψ v := by
  intro k _ _ _ _ i t ψ τ σ u hu v
  let L : (τ.V ⊗[ℂ] σ.V) →ₗ[ℂ] (τ.V ⊗[ℂ] σ.V) :=
    extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1)
  have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (u : Mir k (i + 1)) : ℂˣ) : ℂ) = 1 := by
    have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) u
    simpa using congrArg Units.val this
  have ha : ∀ a : τ.V, (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (u : Mir k (i + 1)) a = τ.ρ (u : Mir k (i + 1)) a := by
    intro a
    refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
    rw [hd, one_smul]
  have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 = 1 := map_one _
  have hb : ∀ b : σ.V, (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 b = b := fun b => LinearMap.congr_fun hρ b
  have e : ∀ (a : τ.V) (b : σ.V), L (a ⊗ₜ[ℂ] b) = (τ.ρ (u : Mir k (i + 1)) a) ⊗ₜ[ℂ] b := fun a b =>
    (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
      ((u : Mir k (i + 1)), 1) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) (ha a) (hb b))
  have hq : ∀ a : τ.V, (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (u : Mir k (i + 1)) a) =
      (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ a := by
    intro a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    unfold twKer
    apply Submodule.subset_span
    exact ⟨u, a, by simp [hu]⟩
  have key : ∀ w : τ.V ⊗[ℂ] σ.V, qO τ σ ψ (L w) = qO τ σ ψ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      rw [e]
      exact congrArg (fun x => TensorProduct.tmul ℂ x b) (hq a)
  exact key v

end GlobalTheory.CompanionTheory.BZPhiPG
