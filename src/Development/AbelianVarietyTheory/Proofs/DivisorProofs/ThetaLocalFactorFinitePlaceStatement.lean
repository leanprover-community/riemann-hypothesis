module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLocalFactorFinitePlace
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

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.theta_local_factor_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ), (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (S : Finset (Pl (F := F))) (g₁ g₂ g₃ : UA σ G.V'.J) (h₁ h₂ h₃ : UA σ G.W.J), v ∉ S ∧
      g = g₁ * g₂ * g₃ ∧ h = h₁ * h₂ * h₃ ∧ At (evI F) (mat g₁ - 1) ∧ At (evI F) (mat h₁ - 1) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g₂ - 1) = 0) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h₂ - 1) = 0) ∧
      (∀ u : AF F, At (evI F) u → u • (mat g₃ - 1) = 0) ∧ (∀ u : AF F, At (evI F) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat g₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, w ≠ v → w ∉ S → ∀ γ, (mat g₃ * γ * Matrix.transpose (mat h₃) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) ∧
      (∀ w, w ≠ v → w ∉ S → φ w = G.M'.vac w) := by
  exact @GlobalTheory.UnitaryTriSplit.factor_away
