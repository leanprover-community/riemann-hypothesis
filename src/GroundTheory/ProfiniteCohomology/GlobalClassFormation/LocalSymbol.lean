module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupLocal
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum

noncomputable section

variable {K : FiniteSubfield}

theorem exists_eq_one_iff_mem_range_norm (v : InfinitePlace K.1) (b : v.Completion) :
    ∃ g : Gal(AlgebraicClosure v.Completion/v.Completion),
      (g = 1 ↔ b ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)) := by
  by_cases hb : b ∈ Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)
  · exact ⟨1, iff_of_true rfl hb⟩
  · by_contra hne
    have hall : ∀ g : Gal(AlgebraicClosure v.Completion/v.Completion), g = 1 := fun g =>
      by_contra fun hg => hne ⟨g, iff_of_false hg hb⟩
    have hcard : Nat.card Gal(AlgebraicClosure v.Completion/v.Completion) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => (hall a).trans (hall c).symm⟩, ⟨1⟩⟩
    rw [IsGalois.card_aut_eq_finrank] at hcard
    exact hb ⟨algebraMap v.Completion _ b, by rw [Algebra.norm_algebraMap, hcard, pow_one]⟩

variable (ι : LocalEmbeddings K)

def localSymbolAt : Place K.1 → K.1ˣ → K.1.fixingSubgroup
  | .inr v, a => globalDecomp (v.adicCompletion K.1) (ι.fin v)
      ((GroundTheory.LocalField.localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
        (Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* v.adicCompletion K.1) a)).liftNormal
          (AlgebraicClosure (v.adicCompletion K.1)))
  | .inl v, a => globalDecomp v.Completion (ι.inf v)
      (exists_eq_one_iff_mem_range_norm v (algebraMap K.1 v.Completion (a : K.1))).choose

theorem placeInv_brauerLocal_globalCupClass (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) :
    ∀ v : Place K.1, placeInv v (brauerLocal ι (globalCupClass χ a) v) =
      χ (Additive.ofMul (localSymbolAt ι v a))
  | .inr v => placeInv_brauerLocal_globalCupClass_inr ι v χ a _ fun y hy =>
      (AlgEquiv.liftNormal_commutes _ _ (⟨y, hy⟩ : GroundTheory.LocalField.maximalAbelianExtension
        (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))))
  | .inl v => placeInv_brauerLocal_globalCupClass_inl ι v χ a _
      (exists_eq_one_iff_mem_range_norm v (algebraMap K.1 v.Completion (a : K.1))).choose_spec

theorem brauerSumInv_globalCupClass (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) :
    brauerSumInv ι (globalCupClass χ a) = ∑ᶠ v : Place K.1, χ (Additive.ofMul (localSymbolAt ι v a)) := by
  classical
  set x := brauerLocal ι (globalCupClass χ a) with hx
  have hsum : brauerSumInv ι (globalCupClass χ a) = ∑ v ∈ x.support, placeInv v (x v) := by
    change sumPlaceInv K x = _
    conv_lhs => rw [← DFinsupp.sum_single (f := x)]

    rw [DFinsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact sumPlaceInv_of v (x v)
  rw [hsum, finsum_eq_sum_of_support_subset _ (s := x.support) ?_]
  · exact Finset.sum_congr rfl fun v _ => placeInv_brauerLocal_globalCupClass ι χ a v
  · intro v hv
    rw [Function.mem_support, ← placeInv_brauerLocal_globalCupClass] at hv
    rw [Finset.mem_coe, DFinsupp.mem_support_iff]
    intro h
    exact hv (by rw [h, map_zero])

end

end GroundTheory.ProfCoh
