module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RealConjFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inv_mem_UAt {n : ℕ} {X : Spc F E n} {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) :
    g⁻¹ ∈ UAt σ X (evI F) := by
  intro u hu
  have h1 : u • (mat g - 1) = 0 := hg u hu
  have hm : mat g⁻¹ * mat g = 1 := by simp [mat]
  have : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, hm, Matrix.mul_one, neg_sub]
  rw [this, smul_neg, ← Matrix.mul_smul, h1, Matrix.mul_zero, neg_zero]

theorem acts_comp {κ : Type} [Fintype κ] {A B : Module.End ℂ ((κ → AF F) → ℂ)}
    (hA : ∀ Φ ∈ schA F κ, A Φ ∈ schA F κ) {f f₁ f₂ : SInf F κ}
    (h₁ : Acts (evI F) A (⇑f) (⇑f₁)) (h₂ : Acts (evI F) B (⇑f₁) (⇑f₂)) :
    Acts (evI F) (B * A) (⇑f) (⇑f₂) := by
  intro r hr
  have e₁ := h₁ r hr
  have hr₁ : Rest (evI F) (⇑f₁) r := ⟨hr.1, by rw [← e₁]; exact hA _ hr.2⟩
  rw [Module.End.mul_apply, e₁]
  exact h₂ r hr₁

end GlobalTheory.RealConjFac
