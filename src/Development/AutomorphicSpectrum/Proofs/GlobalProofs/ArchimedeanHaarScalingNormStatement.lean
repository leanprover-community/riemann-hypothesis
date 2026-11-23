module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_local_approximate_identity : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (AF F), IsCovolOne db → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → Ainf F → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : Fv F v) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : Fv F v)).smallSets) ∧ (∀ k, Integrable (Coef.fouA ψ db (Coef.testT (ρ k) S (U k))) db ∧ ∀ z, ∫ b, Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b * ψ (b * z) ∂db = Coef.testT (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, Coef.testT (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) * ∏ v ∈ S, (((lam v) (U k v)).toReal : ℂ)) ∧ (∀ k b, ‖Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b‖ ≤ ‖∫ y, Coef.testT (ρ k) S (U k) y ∂db‖) ∧ ∀ b, Filter.Tendsto (fun k => Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b / ∫ y, Coef.testT (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((Coef.intF S).indicator (fun _ => (1 : ℂ)) (sndA F b))) := by
  exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx
