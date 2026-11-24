module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegative
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

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.PullCoord

theorem lintegral_thetaMeas_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ 𝓕 hμ h𝓕 S T hST Φ hΦ
  rw [_root_.GlobalTheory.CompanionTheory.SW.ThetaLint.theta_lint_eq F E σ hσ M J hJ μ 𝓕 hμ h𝓕 1 T Φ hΦ]
  have hb := RatCoord.ofF_bijective (M := M) b
  let e : S ≃ T := Equiv.ofBijective (fun x => ⟨ofF b x.1, (hST x.1).2 x.2⟩) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (hb.1 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y.1
      exact ⟨⟨x, (hST x).1 (hx ▸ y.2)⟩, Subtype.ext hx⟩)
  have hsum : ∀ h : HA (AF F) σ J,
      ∑' X : T, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))
        = ∑' x : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (ofF b x.1))) := fun h =>
    (e.tsum_eq (fun X : T =>
      Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E))))).symm
  simp only [hsum, prH, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.SW.BB.PullCoord
