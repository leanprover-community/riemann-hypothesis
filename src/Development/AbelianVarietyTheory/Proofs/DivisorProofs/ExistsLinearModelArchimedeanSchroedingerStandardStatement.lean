module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandard
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  first | exact @GlobalTheory.WeilAdm.RealModel.exists_model | exact GlobalTheory.WeilAdm.RealModel.exists_model | (intros; apply GlobalTheory.WeilAdm.RealModel.exists_model <;> assumption)
