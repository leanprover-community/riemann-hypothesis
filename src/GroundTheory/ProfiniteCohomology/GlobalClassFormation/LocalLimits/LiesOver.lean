module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
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

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.SemiLocal FiniteSubfield

noncomputable section

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]

instance isScalarTower_finiteSubfield_of_fact : IsScalarTower K.1 F.1 E.1 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl


variable (F E) in
def completionEmbeddingBelow (u : PlacesOver F.1 v)
    [(placeOfEmbedding ι E).1.asIdeal.LiesOver u.1.asIdeal] :
    u.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1) :=
  { (completionEmbedding ι E).toRingHom.comp (completionMap u.1 (placeOfEmbedding ι E).1) with
    commutes' a := by
      change completionEmbedding ι E (completionMap u.1 (placeOfEmbedding ι E).1
        (completionMap v u.1 a)) = _
      rw [AdeleBaseChange.completionMap_completionMap v u.1 (placeOfEmbedding ι E).1 a]
      exact (completionEmbedding ι E).commutes a }

theorem completionEmbeddingBelow_apply (u : PlacesOver F.1 v)
    [(placeOfEmbedding ι E).1.asIdeal.LiesOver u.1.asIdeal] (a : u.1.adicCompletion F.1) :
    completionEmbeddingBelow ι F E u a =
      completionEmbedding ι E (completionMap u.1 (placeOfEmbedding ι E).1 a) :=
  rfl

theorem completionEmbeddingBelow_algebraMap (u : PlacesOver F.1 v)
    [(placeOfEmbedding ι E).1.asIdeal.LiesOver u.1.asIdeal] (x : F.1) :
    completionEmbeddingBelow ι F E u (algebraMap F.1 _ x) = ι x := by
  rw [completionEmbeddingBelow_apply, completionMap_algebraMap,
    IsScalarTower.algebraMap_apply F.1 E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1),
    completionEmbedding_algebraMap]
  rfl

theorem below_placeOfEmbedding_liesOver :
    (AdeleBaseChange.below F.1 (placeOfEmbedding ι E).1).asIdeal.LiesOver v.asIdeal := by
  rw [← AdeleBaseChange.below_eq_iff, AdeleBaseChange.below_below,
    AdeleBaseChange.below_eq_iff]
  exact (placeOfEmbedding ι E).2

theorem below_placeOfEmbedding :
    (⟨AdeleBaseChange.below F.1 (placeOfEmbedding ι E).1, below_placeOfEmbedding_liesOver ι⟩ :
      PlacesOver F.1 v) = placeOfEmbedding ι F :=
  eq_placeOfEmbedding ι F (completionEmbeddingBelow ι F E _)
    (completionEmbeddingBelow_algebraMap ι _)

instance liesOver_placeOfEmbedding :
    (placeOfEmbedding ι E).1.asIdeal.LiesOver (placeOfEmbedding ι F).1.asIdeal := by
  rw [← below_placeOfEmbedding ι (F := F) (E := E)]
  exact AdeleBaseChange.liesOver_below _

theorem completionEmbedding_completionMap (a : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    completionEmbedding ι E (completionMap (placeOfEmbedding ι F).1 (placeOfEmbedding ι E).1 a) =
      completionEmbedding ι F a := by
  have : completionEmbeddingBelow ι F E (placeOfEmbedding ι F) = completionEmbedding ι F :=
    algHom_ext_adicCompletion F fun x ↦ by
      rw [completionEmbeddingBelow_algebraMap, completionEmbedding_algebraMap]
  exact DFunLike.congr_fun this a

end

end GroundTheory.ProfCoh
