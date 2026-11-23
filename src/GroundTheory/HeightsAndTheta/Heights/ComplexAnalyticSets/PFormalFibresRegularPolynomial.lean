module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegularPolynomial
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianPrimeDerivations
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationAdicCompletion
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAdicCompletionRegular
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationCotangentIndependent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularQuotientIndependent
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
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
import Mathlib.RingTheory.RegularLocalRing.Polynomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem FormalFibresRegularPolynomial.proof (hJ : JacobianPrimeDerivations.Statement)
    (hE : DerivationAdicCompletion.Statement) (hC : AdicCompletionRegular.Statement)
    (hI : DerivationCotangentIndependent.Statement) (hQ : RegularQuotientIndependent.Statement) :
    FormalFibresRegularPolynomial.Statement := by
  intro k _ n M hM P _
  let B := MvPolynomial (Fin n) k
  let Bh := AdicCompletion M B
  let L := Localization.AtPrime P
  obtain ⟨h, f, D, s, hfp, hs, hsp, hdet⟩ := hJ k n (P.comap (algebraMap B Bh)) (Ideal.comap_isPrime _ _)
  choose D' hD' using fun j => hE B M (D j)
  have : IsRegularLocalRing Bh := hC B inferInstance M inferInstance
  have : IsRegularLocalRing L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime P
  have hdet' : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))).det ∉ P := by
    have hm : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))) =
        (algebraMap B Bh).mapMatrix (Matrix.of fun i j => D j (f i)) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact hD' j (f i)
    rw [hm, ← RingHom.map_det]
    exact hdet
  have hmem : ∀ i, algebraMap Bh L (algebraMap B Bh (f i)) ∈ maximalIdeal L := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mpr (hfp i)
  have hreg := hQ L h _ hmem (hI Bh P h D' (fun i => algebraMap B Bh (f i)) hfp hdet')
  have heq : Ideal.span (Set.range fun i => algebraMap Bh L (algebraMap B Bh (f i))) =
      Ideal.map (algebraMap Bh L) (Ideal.map (algebraMap B Bh) (P.comap (algebraMap B Bh))) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hfp i))
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap Bh L (algebraMap B Bh s)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff L P _).mpr hs
      have hsx := Ideal.mem_map_of_mem ((algebraMap Bh L).comp (algebraMap B Bh)) (hsp x hx)
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at hsx
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hsx
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq heq)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
