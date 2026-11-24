module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfDefs
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

namespace GroundTheory.ProfCoh

open NumberField GroundTheory.Global FiniteSubfield

open scoped NumberField.LiesOver

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.Completion)
  {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]

theorem comap_liesOver (w' : v.placesOver E.1) :
    ((w' : NumberField.InfinitePlace E.1).comap (algebraMap F.1 E.1)).LiesOver v := by
  have : IsScalarTower K.1 F.1 E.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, ← NumberField.InfinitePlace.comap_comp,
    ← IsScalarTower.algebraMap_eq, ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
  exact w'.2

theorem completionMap_algebraMap_completion (u : NumberField.InfinitePlace F.1)
    (w' : NumberField.InfinitePlace E.1) [w'.LiesOver u] [u.LiesOver v] [w'.LiesOver v]
    (c : v.Completion) :
    AbsoluteValue.Completion.map u.1 w'.1 (algebraMap v.Completion u.Completion c) =
      algebraMap v.Completion w'.Completion c := by
  have : IsScalarTower K.1 F.1 E.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver v.1 u.1,
    AbsoluteValue.Completion.algebraMap_eq_of_liesOver v.1 w'.1,
    AbsoluteValue.Completion.map_map]


variable (F E) in
def infCompletionEmbeddingBelow (u : v.placesOver F.1)
    [(infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1)] :
    (u : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion :=
  { (infCompletionEmbedding ι E).toRingHom.comp
      (AbsoluteValue.Completion.map u.1.1 (infPlaceOfEmbedding ι E).1.1) with
    commutes' c := by
      change infCompletionEmbedding ι E (AbsoluteValue.Completion.map u.1.1
        (infPlaceOfEmbedding ι E).1.1 (algebraMap v.Completion _ c)) = _
      rw [completionMap_algebraMap_completion]
      exact (infCompletionEmbedding ι E).commutes c }

theorem infCompletionEmbeddingBelow_algebraMap (u : v.placesOver F.1)
    [(infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1)] (x : F.1) :
    infCompletionEmbeddingBelow ι F E u (algebraMap F.1 _ x) = ι x := by
  change infCompletionEmbedding ι E (AbsoluteValue.Completion.map u.1.1
    (infPlaceOfEmbedding ι E).1.1 (algebraMap F.1 u.1.Completion x)) = ι x
  have hx : ι (algebraMap F.1 E.1 x : E.1) = ι x := rfl
  simpa only [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, AbsoluteValue.Completion.map_coe, WithAbs.map_apply,
    WithAbs.ofAbs_toAbs] using
    (infCompletionEmbedding_algebraMap ι E (algebraMap F.1 E.1 x)).trans hx

instance liesOver_infPlaceOfEmbedding :
    (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) := by
  have hu := comap_liesOver (F := F) (infPlaceOfEmbedding ι E)
  let u : v.placesOver F.1 := ⟨_, hu⟩
  have : (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1) :=
    (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq _ _).2 rfl
  have h := eq_infPlaceOfEmbedding ι F (infCompletionEmbeddingBelow ι F E u)
    (infCompletionEmbeddingBelow_algebraMap ι u)
  rw [← h]
  exact this

theorem infCompletionEmbedding_completionMap
    (a : (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion) :
    infCompletionEmbedding ι E (AbsoluteValue.Completion.map
      (infPlaceOfEmbedding ι F).1.1 (infPlaceOfEmbedding ι E).1.1 a) =
      infCompletionEmbedding ι F a := by
  have : infCompletionEmbeddingBelow ι F E (infPlaceOfEmbedding ι F) = infCompletionEmbedding ι F :=
    algHom_ext_infCompletion F fun x ↦ by
      rw [infCompletionEmbeddingBelow_algebraMap, infCompletionEmbedding_algebraMap]
  exact DFunLike.congr_fun this a

end

end GroundTheory.ProfCoh
