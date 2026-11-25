module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
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
import Mathlib.Tactic.Linter.Style
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

noncomputable section
namespace GlobalTheory.UCls.KGrp
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isUA_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) : IsUA c G g⁻¹ := by
  refine ⟨isUnit_nonsing_inv_det g hg.1, fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]

theorem isKM_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have h1 : k * k⁻¹ = 1 := mul_nonsing_inv k hk.1.1
  have h2 : k⁻¹ * k = 1 := nonsing_inv_mul k hk.1.1
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [mulVec_mulVec, h2, one_mulVec, smul_neg, ← e]; abel
  · obtain ⟨z, hz, e⟩ := hk.2.1 x hx
    refine ⟨k *ᵥ x, ?_, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    have : k *ᵥ x = x + M • z := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hz M)

end GlobalTheory.UCls.KGrp
