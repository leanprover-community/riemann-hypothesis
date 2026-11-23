module

public import GroundTheory.PAdicHodge.BdRField
public import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

section Abstract

variable {S R E D : Type*} [CommRing S] [CommRing R] [CommRing E] [CommRing D]

theorem sub_eq_map_of_pow_mul {F : Type*} [Field F] (j : D →+* F) {T w c a : D} {z X : F} {n : ℕ}
    (hT : j T ≠ 0) (hX : j T ^ n * X = j a) (hz : z * j T ^ n = j w) (hc : c * T ^ n = a - w) :
    X - z = j c := by
  apply mul_right_cancel₀ (pow_ne_zero n hT)
  rw [sub_mul, mul_comm X, hX, hz, ← map_sub, ← hc, map_mul, map_pow]

end Abstract

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)





include hζ in

theorem exists_mul_pow_fontaineT_eq (z : 𝔹dR) :
    ∃ (n : ℕ) (w : 𝔹), z * algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ n = algebraMap 𝔹 𝔹dR w := by
  have := IsPerfectoidField.isLocalization_away_bDeRham (maximalIdeal_eq_span_fontaineT hε hζ)
  obtain ⟨⟨w, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (fontaineT ε hε)) z
  obtain ⟨n, hn⟩ := s.2
  simp only at hn hs
  rw [← hn] at hs
  refine ⟨n, w, ?_⟩
  rw [← map_pow]
  exact hs



end ACris

end GroundTheory.PAdicHodge
