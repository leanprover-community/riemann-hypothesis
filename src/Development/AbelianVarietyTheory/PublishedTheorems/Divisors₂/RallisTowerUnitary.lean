module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def RallisTowerUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin m) (Fin m) E),
    (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 →
  ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW m →
  ∀ f : UA σ JW → ℂ,
    (∃ (c₀ : E) (K : Subgroup (GAd σ (c₀ • JW.map σ))) (φ : GAd σ (c₀ • JW.map σ) → ℂ), IsHermND σ (c₀ • JW.map σ) ∧
      GlobalTheory.UAut.IsMaxCpt σ (c₀ • JW.map σ) K ∧ GlobalTheory.UAut.IsAut σ (c₀ • JW.map σ) K φ ∧
      GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • JW.map σ) φ ∧
      ∀ (h : UA σ JW) (h' : GAd σ (c₀ • JW.map σ)), h.1 = h'.1 → φ h' = f h) →
    (∀ (n₁ k : ℕ) (J₁ : Matrix (Fin n₁) (Fin n₁) E), 1 ≤ k → n₁ + 2 * k = n → (∀ i j, σ (J₁ j i) = J₁ i j) → J₁.det ≠ 0 →
      ∀ co₁ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n₁ × Fin m),
        (∀ x : Matrix (Fin n₁) (Fin m) E, ∃ y z : Fin n₁ × Fin m → F,
          co₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om₁ : UA σ J₁ × UA σ JW →* Module.End ℂ ((Fin n₁ × Fin m → AF F) → ℂ),
        IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co₁ χX χW om₁ →
      ∀ Φ₁ ∈ schA F (Fin n₁ × Fin m), ∀ (g : UA σ J₁) (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ JW) 𝓕 μ → ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om₁ (g, h) Φ₁)) ∂μ = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin m),
    (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
  ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ),
    IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co χX χW om →
  ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
    IsFundamentalDomain (ratU σ JW) 𝓕 μ →
  ∀ c : E, IsHermND σ (c • JX.map σ) → ∀ th : GAd σ (c • JX.map σ) → ℂ,
    (∀ (g : UA σ JX) (g' : GAd σ (c • JX.map σ)), g.1 = g'.1 →
      th g' = ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ) →
    GlobalTheory.SiegelSet.IsCuspidal σ (c • JX.map σ) th

end GlobalTheory.Published

end
