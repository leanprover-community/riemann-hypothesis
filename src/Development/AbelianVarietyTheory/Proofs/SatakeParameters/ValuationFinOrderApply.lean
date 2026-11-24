module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ColPeriod

theorem valuation_finOrder_apply {G K : Type} [Group G] [Field K] [NumberField K] (ξ : G →* Kˣ) (hξ : IsOfFinOrder ξ)
    (w : HeightOneSpectrum (𝓞 K)) (y : G) : w.valuation K ((ξ y : Kˣ) : K) = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hξ
  have h1 : (ξ y) ^ n = 1 := by
    have := congrArg (fun φ : G →* Kˣ => φ y) h
    simpa using this
  have h2 : (w.valuation K ((ξ y : Kˣ) : K)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').1 h2

theorem twistUnit : TwistUnit := by
  intro F E K _ _ _ _ _ _ _ S mu P w
  have hfin : IsOfFinOrder (mu : Chr F E K) := mu.2.1.1.1.2
  let v : HeightOneSpectrum (𝓞 F) := P.under (𝓞 F)
  have hv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  constructor
  · unfold unifVal
    split_ifs with h
    · obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
        have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
        simpa using this
      obtain ⟨y, y₀, h1, h2, h3, h4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P v b hv
      rw [← h.choose_spec v hv y y₀ b h1 hb hb2 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp
  · unfold qValC
    split_ifs with h
    · obtain ⟨y, y₀, h1, h2, h3, h4⟩ :=
        GlobalTheory.SuppIdele.exists_supported_idele F E P v ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) hv
      rw [← h.choose_spec v hv y y₀ h1 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp

end GlobalTheory.ColPeriod
