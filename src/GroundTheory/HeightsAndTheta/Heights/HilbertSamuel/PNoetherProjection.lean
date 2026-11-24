module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNoetherProjection
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
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem NoetherProjection.proof : NoetherProjection.Statement := by
  intro σ _ P hP
  have : Nontrivial (MvPolynomial σ ℚ ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ P)
  choose ℓ hℓ using fun j => Ideal.Quotient.mk_surjective (g (X j))
  have hcomp : (Ideal.Quotient.mkₐ ℚ P).comp (aeval ℓ) = g := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [hℓ]
  have hcompR : (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom = g.toRingHom := by
    rw [← hcomp]
    rfl
  refine ⟨s, ℓ, ?_, ?_⟩
  · intro q hq
    apply hinj
    rw [map_zero, ← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · intro f
    obtain ⟨p, hpm, hp⟩ := hint (Ideal.Quotient.mk P f)
    refine ⟨p, hpm, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, hcompR]
    exact hp

end GroundTheory.Heights₂.Heights.HilbertSamuel
