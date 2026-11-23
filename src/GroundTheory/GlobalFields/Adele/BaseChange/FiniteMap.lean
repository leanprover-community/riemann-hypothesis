module

public import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (K) in
def below (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.under (𝓞 K)
  isPrime := Ideal.IsPrime.under (𝓞 K) w.asIdeal
  ne_bot := Ideal.under_ne_bot (𝓞 K) w.ne_bot

instance liesOver_below (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (below K w).asIdeal :=
  ⟨rfl⟩


omit [NumberField K] [NumberField L] in
theorem below_eq_iff (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) :
    below K w = v ↔ w.asIdeal.LiesOver v.asIdeal := by
  constructor
  · rintro rfl
    infer_instance
  · intro h
    exact HeightOneSpectrum.ext h.over.symm

theorem tendsto_below : Tendsto (below K (L := L)) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦
    ((Set.finite_range (Subtype.val : PlacesOver (L := L) v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ⟨⟨w, (below_eq_iff w v).1 hw⟩, rfl⟩).to_subtype

theorem completionMap_congr {v v' : HeightOneSpectrum (𝓞 K)} (h : v = v')
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v'.asIdeal]
    (a : FiniteAdeleRing (𝓞 K) K) :
    completionMap v w (a v) = completionMap v' w (a v') := by
  subst h
  rfl

theorem mapsTo_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Set.MapsTo (completionMap v w) (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [valued_completionMap]
  exact pow_le_one' hx _


variable (K L) in
def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (B₁ := fun v ↦ v.adicCompletionIntegers K) (B₂ := fun w ↦ w.adicCompletionIntegers L)
    (below K) tendsto_below (fun w ↦ completionMap (below K w) w)
    (hφ := .of_forall fun w ↦ mapsTo_completionMap (below K w) w)

@[simp]
theorem finiteAdeleMap_apply (x : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleMap K L x w = completionMap (below K w) w (x (below K w)) :=
  rfl

theorem continuous_finiteAdeleMap : Continuous (finiteAdeleMap K L) :=
  RestrictedProduct.mapAlong_continuous _ _ (below K) tendsto_below _
    (.of_forall fun w ↦ mapsTo_completionMap (below K w) w) fun w ↦ continuous_completionMap (below K w) w

theorem finiteAdeleMap_algebraMap (k : K) :
    finiteAdeleMap K L (algebraMap K _ k) = algebraMap L _ (algebraMap K L k) := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  exact (completionMap_algebraMap (below K w) w k).trans
    (IsScalarTower.algebraMap_apply K L (w.adicCompletion L) k)

end AdeleBaseChange

end

end GroundTheory.Global
