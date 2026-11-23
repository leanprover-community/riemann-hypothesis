module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryAverageFockPolynomialJetFunctional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix

theorem _root_.GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  first | exact @GlobalTheory.AvgJet.avg_jet | exact GlobalTheory.AvgJet.avg_jet | (intros; apply GlobalTheory.AvgJet.avg_jet <;> assumption)
