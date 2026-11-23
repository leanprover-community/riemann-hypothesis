module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt

namespace GlobalTheory.AmpleHtLow

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem small_of_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ), 1 ≤ m → ∀ (s : (L.pow m).B.Sec), ∃ c : ℝ,
      s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec := by
  intro k _ X p D hX L m hm s
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range (((L.pow m).cInf σ).continuous_nsq s)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  have hK' : ∀ σ, K σ ≤ ∑ τ, |K τ| + 1 := fun σ => by
    have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]
  have h1 : (1 : ℝ) ≤ ∑ τ, |K τ| + 1 := by
    linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  set K' : ℝ := ∑ τ, |K τ| + 1
  have hl : 0 ≤ Real.log K' := Real.log_nonneg h1
  have hpos : 0 < K' := by linarith
  refine ⟨-(Real.log K' / 2), fun σ y => ?_⟩
  refine (le_of_eq (nsq_shift_pow L (fun _ => -(-(Real.log K' / 2))) (fun _ => rfl) m σ (CxPts.secVal p σ s) y)).trans ?_
  have h0 : 0 ≤ ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y := by unfold Weight.nsq; positivity
  have h2 : Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2)))) ≤ K'⁻¹ := by
    rw [show -(2 * (m : ℝ) * -(-(Real.log K' / 2))) = -((m : ℝ) * Real.log K') by ring,
      ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_log hpos]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  calc ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y * Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2))))
      ≤ K' * K'⁻¹ := mul_le_mul ((hK σ y).trans (hK' σ)) h2 (Real.exp_pos _).le hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

end GlobalTheory.AmpleHtLow

end
