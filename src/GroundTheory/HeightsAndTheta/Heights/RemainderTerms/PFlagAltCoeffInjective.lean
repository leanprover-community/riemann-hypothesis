module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagAltCoeffInjective.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagAltCoeffInjective.Statement := by
  classical
  intro f N P α hP hc τ i j hij
  simp only at hij
  by_contra hne
  let w : Fin f → Equiv.Perm (Fin N) := Function.update 1 τ (Equiv.swap i j)
  have hsign : blockSign f N w = -1 := by
    unfold blockSign
    rw [Finset.prod_eq_single τ]
    · simp [w, Equiv.Perm.sign_swap hne]
    · intro b _ hb
      simp [w, Function.update_of_ne hb]
    · simp
  have hα : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α := by
    ext ⟨σ, k⟩
    change α (σ, w σ k) = α (σ, k)
    by_cases hσ : σ = τ
    · subst hσ
      simp only [w, Function.update_self]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left]; exact hij.symm
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Equiv.swap_apply_right]; exact hij
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    · simp [w, Function.update_of_ne hσ]
  have key := h1 f N w P α
  rw [hα, hP w, hsign, MvPolynomial.coeff_smul] at key
  have : AddMonoidAlgebra.coeff P α = 0 := by
    have h2 : (2 : ℚ) * AddMonoidAlgebra.coeff P α = 0 := by
      rw [smul_eq_mul] at key
      linarith
    simpa using h2
  exact hc this

end RestTerms

end GroundTheory.Heights₂.Heights
