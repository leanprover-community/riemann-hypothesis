import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Mem.Th
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

section Core

variable {X : Type} [MeasurableSpace X] {ν : Measure X}

def HasRows (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (β : X → Lp ℂ 2 ν) : Prop :=
  ∀ φ : Lp ℂ 2 ν, B φ =ᵐ[ν] fun x => ⟪β x, φ⟫_ℂ

def IsKernelOf (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (K : X → X → ℂ) : Prop :=
  (∀ x, MemLp (K x) 2 ν) ∧ ∀ φ : Lp ℂ 2 ν, T φ =ᵐ[ν] fun x => ∫ z, K x z * φ z ∂ν

def TraceIsDiagonal (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (K : X → X → ℂ) : Prop :=
  IsTraceClass T ∧ Integrable (fun x => K x x) ν ∧ trace T = ∫ x, K x x ∂ν

end Core

def TraceKernelCore : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    [ν.IsOpenPosMeasure] [IsSeparable ν] (n : ℕ) (B C : Fin n → (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (β γ : Fin n → X → Lp ℂ 2 ν),
    (∀ i, IsHilbertSchmidt (B i)) → (∀ i, IsHilbertSchmidt (C i)) →
    (∀ i, Continuous (β i)) → (∀ i, Continuous (γ i)) →
    (∀ i, HasRows (B i) (β i)) → (∀ i, HasRows (ContinuousLinearMap.adjoint (C i)) (γ i)) →
      (∀ i, IsKernelOf (B i ∘L C i) (fun x z => ⟪β i x, γ i z⟫_ℂ) ∧
        TraceIsDiagonal (B i ∘L C i) fun x z => ⟪β i x, γ i z⟫_ℂ) ∧
      ∀ K : X → X → ℂ, Continuous (Function.uncurry K) → IsKernelOf (∑ i, B i ∘L C i) K →
        TraceIsDiagonal (∑ i, B i ∘L C i) K

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCcInf (θ : InfF D) (V : HSp D) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧
    (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, f (g * k) = f g) ∧
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def MapsIntoCusp (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA D V → ℂ) : Prop :=
  ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ

def CuspTraceClass (θ : InfF D) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : Prop :=
  ∀ f, IsCcInf θ V f → IsTraceClass (RcuspOp V μ f)

def TraceKernelAt (θ : InfF D) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : Prop :=
  ∀ f, IsCcInf θ V f → MapsIntoCusp V μ f → MapsIntoCusp V μ (starFn f) →
    TraceIsDiagonal (ν := autMeasure V μ) (RopG V μ f) (kernelQ (GQ V) f)

def TraceKernel : Prop :=
  ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    CuspTraceClass θ V μ → TraceKernelAt θ V μ

def TraceKernelUncond : Prop :=
  ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    TraceKernelAt θ V μ


example (V : HSp D) (f : GA D V → ℂ) (x : GA D V) :
    kernelQ (GQ V) f (mk _ x) (mk _ x) = ∑' γ : GQ V, f (x⁻¹ * γ * x) := kernelQ_mk f x x




end GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

end
