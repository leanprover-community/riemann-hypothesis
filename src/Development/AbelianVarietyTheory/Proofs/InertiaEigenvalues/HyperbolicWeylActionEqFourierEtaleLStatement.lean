module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleL
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

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  first | exact @GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | exact GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | (intros; apply GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB <;> assumption)
