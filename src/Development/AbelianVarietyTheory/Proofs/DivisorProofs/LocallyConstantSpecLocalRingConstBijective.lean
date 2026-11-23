module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.LocallyConstant.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem locallyConstant_spec_local_eq_closedPoint {R A : Type} [CommRing A] [IsLocalRing A]
    (f : LocallyConstant (Spec (CommRingCat.of A)) R) (x : Spec (CommRingCat.of A)) :
    f x = f (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
  have hx : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum A).isPrime.ne_top)
  have ho : IsOpen (f ⁻¹' {f (IsLocalRing.closedPoint A : PrimeSpectrum A)}) := f.isLocallyConstant _
  exact hx.mem_open ho rfl

theorem locallyConstant_spec_local_bijective :
    ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A],
      Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  intro R A _ _
  refine ⟨fun c d h => ?_, fun f => ⟨f (IsLocalRing.closedPoint A : PrimeSpectrum A), ?_⟩⟩
  · have := congrArg (fun g : LocallyConstant (Spec (CommRingCat.of A)) R =>
      g (IsLocalRing.closedPoint A : PrimeSpectrum A)) h
    exact this
  · ext x
    simp only [LocallyConstant.coe_const, Function.const_apply]
    exact (locallyConstant_spec_local_eq_closedPoint f x).symm

end GlobalTheory
