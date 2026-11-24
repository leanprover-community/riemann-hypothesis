module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
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

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.EvUniq

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def FinRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (v : Pl F)
    (T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ) : Prop :=
  (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) φ φ₁ →
      ∀ χ₁ ∈ SB (Fin n × Fin d₁ → Fv F v), Acts (evFin F v) (M₁.co.rho B.ψ z) (T φ) χ₁ → T φ₁ = χ₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → T φ₁ = T φ

def InfRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁)
    (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)) : Prop :=
  (∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) f f₁ →
      ∀ g₁ : SInf F (Fin n × Fin d₁), Acts (evI F) (M₁.co.rho B.ψ z) (T f) g₁ → T f₁ = g₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (M.co.rho B.ψ u) f f₁ → T f₁ = T f

end GlobalTheory.ThK.EvUniq
