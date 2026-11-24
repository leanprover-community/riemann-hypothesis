module

public import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.Adele.Approximation
public import GroundTheory.GlobalFields.LocalAtPlace
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

variable (K : Type*) [Field K] [NumberField K]

instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun v ↦ isOpen_adicCompletionIntegers v⟩

instance locallyCompactSpace_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.locallyCompactSpace_of_addGroup
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (.of_forall fun v ↦ isCompact_adicCompletionIntegers v)

theorem t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstance

instance locallyCompactSpace_adeleRing : LocallyCompactSpace 𝔸[K] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

theorem t2Space_adeleRing : T2Space 𝔸[K] :=
  inferInstance

instance IdeleGroup.locallyCompactSpace : LocallyCompactSpace (IdeleGroup K) :=
  inferInstance

instance locallyCompactSpace_units_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K)ˣ :=
  inferInstance

instance locallyCompactSpace_units_infiniteAdeleRing :
    LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  inferInstance

end GroundTheory.Global
