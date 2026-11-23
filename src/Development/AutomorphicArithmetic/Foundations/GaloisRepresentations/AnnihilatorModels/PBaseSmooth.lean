module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseSmooth_of :
    SmoothClosed → SmoothReduced → BaseOfSmooth := by
  intro hC hR l O R _ _ _ _ _ _ ϖ hϖ hl _
  have hflat : Module.Flat O R := Algebra.Smooth.flat O R
  have hlO : (l : O) ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hl
  refine ⟨?_, hC l O R hl, ?_⟩
  · have hreg : IsSMulRegular R (l : O) := Module.Flat.isSMulRegular_of_nonZeroDivisors hlO
    have key : ∀ x : R, (l : R) * x = 0 → x = 0 := by
      intro x hx
      apply hreg
      simp only [Algebra.smul_def, map_natCast, mul_zero]
      exact hx
    rw [mem_nonZeroDivisors_iff]
    exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩
  · rw [Ideal.isRadical_iff_quotient_reduced]
    have hspan : Ideal.span {(algebraMap O R) ϖ} = (IsLocalRing.maximalIdeal O).map (algebraMap O R) := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]
    rw [hspan]
    haveI : Algebra.Smooth (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R) :=
      Algebra.Smooth.baseChange O R (IsLocalRing.ResidueField O)
    have hred : IsReduced (IsLocalRing.ResidueField O ⊗[O] R) :=
      hR (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R)
    haveI : IsReduced ((O ⧸ IsLocalRing.maximalIdeal O) ⊗[O] R) := hred
    let e := ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (IsLocalRing.maximalIdeal O)).restrictScalars O).trans
      (Algebra.TensorProduct.comm O R (O ⧸ IsLocalRing.maximalIdeal O))
    exact isReduced_of_injective e.toRingHom e.injective
