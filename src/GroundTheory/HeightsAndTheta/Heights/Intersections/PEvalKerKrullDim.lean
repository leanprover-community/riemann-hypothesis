module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsEvalKerKrullDim
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IntermediateField.algebraAdjoinAdjoin

theorem EvalKerKrullDim.proof : EvalKerKrullDim.Statement := by
  intro K _ ι _ F L _ _ _ y

  let f : MRingOver F ι →ₐ[F] Algebra.adjoin F (Set.range y) :=
    (Subalgebra.equivOfEq _ _ (MvPolynomial.aeval_range y)).toAlgHom.comp (aeval y).rangeRestrict
  have hf : Function.Surjective f :=
    (Subalgebra.equivOfEq _ _ (MvPolynomial.aeval_range y)).surjective.comp
      (AlgHom.rangeRestrict_surjective _)
  have hker : RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L) = RingHom.ker f := by
    ext p
    simp [f, RingHom.mem_ker, Subtype.ext_iff]
  let e : (MRingOver F ι ⧸ RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L)) ≃ₐ[F]
      Algebra.adjoin F (Set.range y) :=
    (Ideal.quotientEquivAlgOfEq F hker).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  have _ : Algebra.FiniteType F (Algebra.adjoin F (Set.range y)) :=
    Algebra.FiniteType.of_surjective f hf
  exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing F
    (IntermediateField.adjoin F (Set.range y))

end GroundTheory.Heights₂.Heights.Inter
