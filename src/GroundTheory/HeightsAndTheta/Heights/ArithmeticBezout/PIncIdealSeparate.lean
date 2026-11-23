module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealSeparate
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFormsThroughPoint
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealNeBotDim
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
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
import Mathlib.RingTheory.TotallySplit
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealSeparate.proof (hZ : IncidenceZeroLocus.Statement) (hT : FormsThroughPoint.Statement)
    (hD : IncIdealNeBotDim.Statement) : IncIdealSeparate.Statement := by
  intro F _ n k P Q hP hQ hne hle q hqQ
  by_contra hqP
  have := hP.isPrime

  obtain ⟨φ, hφ⟩ : ∃ φ : (MvPolynomial (Fin n) F ⧸ P) →ₐ[F] AlgebraicClosure F,
      φ (Ideal.Quotient.mk P q) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqP (Ideal.Quotient.eq_zero_iff_mem.mp
      (FGNullstellensatz.proof F (MvPolynomial (Fin n) F ⧸ P) (Ideal.Quotient.mk P q) h))
  let x : Fin n → AlgebraicClosure F := fun j => φ (Ideal.Quotient.mk P (X j))
  have hev : ∀ g, aeval x g = φ (Ideal.Quotient.mk P g) := by
    intro g
    have h : (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) =
        φ.comp (Ideal.Quotient.mkₐ F P) := by
      ext j
      simp [x]
    rw [h]
    rfl
  have hxq : aeval x q ≠ 0 := by rw [hev]; exact hφ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hxq
    have hc : constantCoeff q = 0 := by
      by_contra hc
      have hmem := hQ.isHomog q hqQ 0
      rw [homogeneousComponent_zero, ← constantCoeff_eq] at hmem
      exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map C))
    rw [h0, aeval_zero, hc, map_zero]

  obtain ⟨u, hux, huQ⟩ := hT F n k Q hQ (hD F n k Q hQ hne) x hx0 ⟨q, hqQ, hxq⟩
  apply huQ
  refine hZ F n k Q hQ.isHomog (AlgebraicClosure F) u fun g hg => ?_
  have hgP := hle hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hgP
  refine hgP u ⟨x, hx0, fun g' hg' => ?_, hux⟩
  rw [hev, Ideal.Quotient.eq_zero_iff_mem.mpr hg', map_zero]

end GroundTheory.Heights₂.Heights
