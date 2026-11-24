module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem SpecialQuotDim.proof : SpecialQuotDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ W hW
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π ≤ W := by
    change RingHom.ker (MvPolynomial.map (IsLocalRing.residue O)) ≤ W
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hW
  have hcomap : (specialIdeal W).comap π = W := by
    change (W.map π).comap π = W
    rw [Ideal.comap_map_of_surjective' _ hsurj, sup_eq_left.2 hker]
  let f := (Ideal.Quotient.mk (specialIdeal W)).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hsurj
  have hkf : RingHom.ker f = W := by
    ext x
    change Ideal.Quotient.mk _ (π x) = 0 ↔ x ∈ W
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hkf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
