module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealPrime.proof (h₁ : IncidenceGeneric.Statement) : IncIdealPrime.Statement := by
  intro F _ n k P hP hrel
  have := hP
  obtain ⟨j, hj⟩ := hrel
  have hξ : genPt P j ≠ 0 := by
    unfold genPt
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) := Pi.single j (genPt P j)⁻¹ with hc
  have hsum : ∑ l, c l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j]
    · simp [hc, inv_mul_cancel₀ hξ]
    · intro b _ hb
      simp [hc, Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hker : incIdeal P k =
      RingHom.ker (aeval (genSubst (k := k) (genPt P) c) :
        MvPolynomial (Fin k × Fin n) F →ₐ[F]
          MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) := by
    ext g
    rw [RingHom.mem_ker]
    exact h₁ F n k P c hsum g
  rw [hker]
  exact RingHom.ker_isPrime _

end GroundTheory.Heights₂.Heights
