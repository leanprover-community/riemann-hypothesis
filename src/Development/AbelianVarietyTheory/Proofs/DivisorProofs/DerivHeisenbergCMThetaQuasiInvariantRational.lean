module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
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

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaDerivQuasi

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.ThetaDerivQuasi

theorem GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f hf L _ _ γ w
  have key : ∀ t : ℝ, Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w) =
      B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
        Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    simp only [Formalism.IndefR.DatumF.heisOF]
    rw [add_assoc, hf.quasi γ (w + L t), GlobalTheory.ThetaDerivQuasi.symplOHF_add_left',
      GlobalTheory.ThetaDerivQuasi.symplOHF_add_right', neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    have h1 : B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) *
        B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L t)) *
      B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w) * f (w + L t)) * h1
  simp_rw [key]
  exact congrFun (deriv_const_mul_field' _) 0

end
