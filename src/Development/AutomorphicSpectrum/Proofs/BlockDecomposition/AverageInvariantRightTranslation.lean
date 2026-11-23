module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
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

noncomputable section

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.AvgRight

theorem avgK_right_invariant : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  intro O _ _ n ϖ φ hφ j
  have hout : ∀ x : GL (Ix n) O,
      φ (Quotient.out (QuotientGroup.mk x : GL (Ix n) O ⧸ Gam2 (n := n) ϖ)) = φ x := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gam2 (n := n) ϖ) x
    rw [hh]
    exact hφ x h.1 h.2
  have hshift : ∀ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ,
      φ (Quotient.out u * j) =
        φ (Quotient.out (u * (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))) := by
    intro u
    rw [← hout (Quotient.out u * j)]
    congr 2
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  unfold avgK
  congr 1
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))
    (f := fun u => φ (Quotient.out u))

end GlobalTheory.CompanionTheory.Jp.AvgRight

end
