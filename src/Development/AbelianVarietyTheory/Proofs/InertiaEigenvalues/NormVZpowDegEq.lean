module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem normV_zpow_deg_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (σ' : Weil h') (σ : Weil h) (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    ((normV v' : ℕ) : ℝ) ^ deg σ' = ((normV v : ℕ) : ℝ) ^ deg σ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨a, b, ha⟩ := σ'.2
  obtain ⟨c, d, hc⟩ := σ.2
  rw [deg_eq ha, deg_eq hc]
  set q' := normV v' with hq'
  set q := normV v with hq
  have hq'0 : 0 < q' := (zero_lt_one.trans (one_lt_normV v'))
  have hq0 : 0 < q := (zero_lt_one.trans (one_lt_normV v))
  have key : ∀ x : Ω, A.valuation x ≤ 1 →
      A.valuation (x ^ (q' ^ a * q ^ d) - x ^ (q ^ c * q' ^ b)) < 1 := by
    intro x hx
    have hy : A.valuation ((σ' : G L Ω) x) ≤ 1 := val_apply_le_one ha.1 hx
    have h1 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (ha.2 x hx) (q ^ d)
    have h2' := hc.2 x hx
    rw [hσ] at h2'
    have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) h2' (q' ^ b)
    rw [← pow_mul, ← pow_mul] at h1 h2
    rw [mul_comm (q ^ d) (q' ^ b)] at h2
    exact cong_trans (cong_symm h1) h2
  have hN : q' ^ a * q ^ d = q ^ c * q' ^ b := by
    rcases lt_trichotomy (q' ^ a * q ^ d) (q ^ c * q' ^ b) with hlt | heq | hgt
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq'0 a) (pow_pos hq0 d)) hlt
      exact absurd (cong_symm (key x hx)) hx'
    · exact heq
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq0 c) (pow_pos hq'0 b)) hgt
      exact absurd (key x hx) hx'
  have hR : ((q' : ℕ) : ℝ) ^ a * ((q : ℕ) : ℝ) ^ d = ((q : ℕ) : ℝ) ^ c * ((q' : ℕ) : ℝ) ^ b := by
    exact_mod_cast hN
  have h1 : ((q' : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((q : ℕ) : ℝ) ≠ 0 := by positivity
  rw [zpow_sub₀ h1, zpow_sub₀ h2, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h2)]
  linarith

end GlobalTheory.LocLanglands

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands
