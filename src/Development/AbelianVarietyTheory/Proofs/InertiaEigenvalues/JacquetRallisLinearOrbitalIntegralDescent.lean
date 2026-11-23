module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCutoffFunctionTorusGLStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportJacquetRallisDescStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportPartialFourierGLBStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorLinearDescentPointOneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearDescentPartialFourierEqFourierDescentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralLinearDescentCutoffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGlOrbitEqFourierEtaleKProdStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ (φ' : A.K × A.K → ℂ) (κ : ℂ), IsTest φ' ∧ ∀ a : A.K, IsUnit a → orbG M f' (sec (A.invK τ p lam a)) = κ * A.orbK m.μK φ' a ∧ orbG M (fourG M ψ f') (sec (A.invK τ p lam a)) = κ * A.orbK m.μK (A.fourK m.μK ψ φ') a := by
  intro F E _ _ _ _ _ A ψ hψ m r M τ p lam hG f' hf'
  have hK : m.μK.IsAddHaarMeasure := m.sdK.1
  obtain ⟨α, hαl, hαc, hα0, hαn⟩ := GlobalTheory.T.exists_cutoff_function_torus_GL F E A r τ p hG lam m.μK hK f' hf'
  obtain ⟨κ₀, hκ⟩ := GlobalTheory.T.jacquetRallisTransferFactor_linearDescentPoint_one F E A r τ p hG lam
  have hF : IsTest (fourG M ψ f') := GlobalTheory.T.isLocallyConstantCompactSupport_partialFourierGLBlock F E r M ψ hψ f' hf'
  have hsupp : ∀ g : GL (Fin r) F, (∃ v w : Fin r → F, fourG M ψ f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) →
      ∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0 := by
    intro g ⟨v, w, h⟩
    by_contra hc
    push_neg at hc
    apply h
    simp only [fourG, hc, zero_mul, MeasureTheory.integral_zero]
  have hsw : LinDesc.desc A M hG lam α (fourG M ψ f') = A.fourK m.μK ψ (LinDesc.desc A M hG lam α f') :=
    funext (GlobalTheory.T.linearDescent_partialFourier_eq_fourier_descent F E A r τ p hG lam M ψ hψ m.μK m.sdK α f' hf' hαl hαc
      (GlobalTheory.T.partialFourier_glOrbit_eq_fourier_etaleKProd F E A r τ p hG lam M ψ hψ m.μK m.sdK f' hf'))
  refine ⟨LinDesc.desc A M hG lam α f', κ₀, GlobalTheory.T.isLocallyConstantCompactSupport_jacquetRallisDescent F E A r τ p hG lam M α f' hf' hαl hαc, fun a ha => ⟨?_, ?_⟩⟩
  · rw [← LinDesc.pt_one F E A r τ p hG lam a]
    exact GlobalTheory.T.orbitalIntegral_linearDescent_cutoff F E A r τ p hG lam M m.μK hK α f' hf' hαl hαc hα0 hαn κ₀ hκ a ha
  · rw [← LinDesc.pt_one F E A r τ p hG lam a, ← hsw]
    exact GlobalTheory.T.orbitalIntegral_linearDescent_cutoff F E A r τ p hG lam M m.μK hK α (fourG M ψ f') hF hαl hαc hα0
      (fun g hg => hαn g (hsupp g hg)) κ₀ hκ a ha

end GlobalTheory.JR.LinDesc
