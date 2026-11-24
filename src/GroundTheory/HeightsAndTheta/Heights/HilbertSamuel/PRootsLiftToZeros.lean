module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsLiftToZeros
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreRest
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem RootsLiftToZeros.proof : RootsLiftToZeros.Statement := by
  intro σ P e ℓ u G hint hG y t ht
  classical
  let A := MvPolynomial σ ℚ ⧸ P
  let α : Polynomial (MvPolynomial (Fin e) ℚ) →+* A :=
    (Ideal.Quotient.mk P).comp (Polynomial.eval₂RingHom (aeval ℓ).toRingHom u)
  letI : Algebra (Polynomial (MvPolynomial (Fin e) ℚ)) A := α.toAlgebra
  have hα : ∀ Q, algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A Q =
      Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) := fun _ => rfl
  have _ : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin e) ℚ)) A := by
    constructor
    intro a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hpm, hp⟩ := hint g
    refine ⟨p.map Polynomial.C, hpm.map _, ?_⟩
    have hc : (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A).comp Polynomial.C =
        (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom :=
      RingHom.ext fun r => by simp [hα]
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  let ev : Polynomial (MvPolynomial (Fin e) ℚ) →+* ℂ := Polynomial.eval₂RingHom (aeval y).toRingHom t
  have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A) ≤ RingHom.ker ev := by
    intro Q hQ
    rw [RingHom.mem_ker, hα, Ideal.Quotient.eq_zero_iff_mem] at hQ
    obtain ⟨H, rfl⟩ := hG Q hQ
    rw [RingHom.mem_ker, map_mul]
    change Polynomial.eval₂ (aeval y).toRingHom t G * ev H = 0
    rw [ht, zero_mul]
  obtain ⟨ψ, hψ⟩ := _root_.UpperTheory.Reformulated.B.Qi28.exists_extend ev hker
  let χ : MvPolynomial σ ℚ →+* ℂ := ψ.comp (Ideal.Quotient.mk P)
  have hχ : χ = (aeval fun i => χ (X i)).toRingHom :=
    MvPolynomial.ringHom_ext
      (fun r => RingHom.congr_fun (Subsingleton.elim (χ.comp C) ((aeval fun i => χ (X i)).toRingHom.comp C)) r)
      (fun i => by simp)
  have key : ∀ Q, χ (Q.eval₂ (aeval ℓ).toRingHom u) = ev Q := fun Q => RingHom.congr_fun hψ Q
  have hz : ∀ g, aeval (fun i => χ (X i)) g = χ g := fun g => (RingHom.congr_fun hχ g).symm
  refine ⟨fun i => χ (X i), fun g hg => ?_, funext fun j => ?_, ?_⟩
  · rw [hz]
    change ψ (Ideal.Quotient.mk P g) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  · have := key (Polynomial.C (X j))
    simp only [Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at this
    rw [hz, this]
    simp [ev]
  · have := key Polynomial.X
    simp only [Polynomial.eval₂_X] at this
    rw [hz, this]
    simp [ev]

end GroundTheory.Heights₂.Heights.HilbertSamuel
