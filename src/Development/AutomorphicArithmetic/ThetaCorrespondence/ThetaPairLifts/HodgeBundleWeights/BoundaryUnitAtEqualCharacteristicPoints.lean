module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSectionStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BoundaryUnitValuationIntegral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DetLineExistsHorizontalSection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BdryUnit
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
theorem boundary_unit_at_equalCharacteristic_points : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ)) → ∃ s₀ : ArchSec U x Z (flatWt Dw τ), ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s₀.sig) = 0 := by
  intro hP hQ2 E _ _ _ H Dw l Xo c r U x hL Z τ _
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := _root_.GlobalTheory.T.detLine_period_flat hP hQ2 E H Dw l Xo c r U x hL Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.T.exists_flatWeight_rule_reads_nonvanishing_detSection E H Dw l Xo c Y Z V τ sig hV hs hnv
  have hnorm := GlobalTheory.T.constant_length_of_reading_horizontal_section E H Dw l Xo c r U x hL Z τ Y V sig f hV hs hnv hh hf hR
  choose b hb hb' using fun σ => hnorm _ (goodEmb_goodOf c σ)
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, fun T io y₀ h0 hZ =>
    _root_.GlobalTheory.T.boundary_unit_valuation_integral hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩
end GlobalTheory.BdryUnit
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.boundary_isUnit_at_eqChar_points : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ)) → ∃ s₀ : ArchSec U x Z (flatWt Dw τ), ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s₀.sig) = 0 := by
  first | exact @_root_.GlobalTheory.BdryUnit.boundary_unit_at_equalCharacteristic_points | exact _root_.GlobalTheory.BdryUnit.boundary_unit_at_equalCharacteristic_points | (intros; apply _root_.GlobalTheory.BdryUnit.boundary_unit_at_equalCharacteristic_points <;> assumption)
end
