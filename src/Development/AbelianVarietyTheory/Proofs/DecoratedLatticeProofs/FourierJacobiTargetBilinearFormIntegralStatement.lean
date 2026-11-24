module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.fourierJacobi_target_bilinear_form_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : c = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (fj : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : Represents ψ ν ρ σ fj B) (_ : BilPos ψ μ (ρ + 1) σ B) (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔ FJInt ψ ν μX μG μ ρ (fun h Ψ Φ₀ => fj Ψ (σ h F) Φ₀) Φ.1 z := by
  first | exact @GlobalTheory.PosOne.FJTarget.target_bilinear | exact GlobalTheory.PosOne.FJTarget.target_bilinear | (intros; apply GlobalTheory.PosOne.FJTarget.target_bilinear <;> assumption)
