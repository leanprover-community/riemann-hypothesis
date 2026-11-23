module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProduct
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → (∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0) → ∀ μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), μU.IsAddHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ ∀ h : HA (Fv F v) σ J → ℝ≥0∞, Measurable h → ∀ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) → ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μ0 ∂μU := by
  first | exact @GlobalTheory.HaarSectionProd.haar_S_local | exact GlobalTheory.HaarSectionProd.haar_S_local | (intros; apply GlobalTheory.HaarSectionProd.haar_S_local <;> assumption)
