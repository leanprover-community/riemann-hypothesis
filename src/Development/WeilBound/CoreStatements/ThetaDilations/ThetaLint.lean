module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaLint
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem theta_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ 𝓕 hμ h𝓕 n S Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm M J hJ (AF F)
  have hm : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  rw [thetaMeas, lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul,
    lintegral_tsum (f := fun (X : S) h => Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)))
      fun X => (hΦ.comp (hm _)).aemeasurable]
  simp only [lintegral_map hΦ (hm _)]

theorem theta_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.theta_int

theorem act_rat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E) :
    ∃ X' : Fin n → Fin M → E, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm

  simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem theta_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}) ∧ thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.theta_inv

end PositivityTheory.PlacePermOperatorBicommutantSpan
