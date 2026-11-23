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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    {m : ℕ} (φ : Fin m → (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ u (∑ i, φ i) = ∑ i, M.co.rho ψ u (φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem rho_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    M.co.rho ψ u 0 = 0 := by
  funext x
  simp only [Darboux.rho, schr, Pi.zero_apply, mul_zero]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ)
    (f c' : SInf F κ) (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c'))
    (T : SInf F κ →L[ℂ] ℂ) : HasDerivAt (fun t => T (c t)) (T c') 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hT := ((T.restrictScalars ℝ).continuous.tendsto c').comp hl
  refine hT.congr fun t => ?_
  simp only [Function.comp_apply, slope_def_module, sub_zero, hc0]
  rw [← map_sub]
  exact (T.restrictScalars ℝ).map_smul t⁻¹ (c t - f)

theorem hasDerivAt_eval {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (y : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t => c t y) (c' y) 0 := by
  have h := hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl
    ((BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))
  simpa using h

theorem hasDerivAt_clm {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (T : SInf F κ →L[ℂ] ℂ) :
    HasDerivAt (fun t => T (c t)) (T c') 0 :=
  hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl T

end GlobalTheory.ThetaLineDeriv

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

end GlobalTheory.ThetaLineDeriv
