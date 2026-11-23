module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfHeisenbergInvariantNorms
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f f' : BBF σ JS JT ξ₀ ψ,
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BBF σ JS JT ξ₀ ψ →L[ℂ] H),
        (∀ w g, ‖Φ (rhoBF σ JS JT ξ₀ ψ hψ w g)‖ = ‖Φ g‖) → ‖Φ f'‖ = ‖Φ f‖) →
      ∫⁻ w in 𝓕, ‖f'.1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f.1 w‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.RealWeilF.lintegral_eq_of_normsF | exact GlobalTheory.RealWeilF.lintegral_eq_of_normsF | (intros; apply GlobalTheory.RealWeilF.lintegral_eq_of_normsF <;> assumption)
