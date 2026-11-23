module

public import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K]

instance secondCountableTopology_infinitePlaceCompletion (w : InfinitePlace K) :
    SecondCountableTopology w.Completion :=
  (Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

noncomputable instance measurableSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    MeasurableSpace w.Completion :=
  borel _

instance borelSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    BorelSpace w.Completion :=
  ⟨rfl⟩

variable [NumberField K]

instance secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology (∀ w : InfinitePlace K, w.Completion))

noncomputable instance measurableSpace_infiniteAdeleRing : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ w : InfinitePlace K, w.Completion))

instance borelSpace_infiniteAdeleRing : BorelSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (BorelSpace (∀ w : InfinitePlace K, w.Completion))

noncomputable instance measurableSpace_finiteAdeleRing :
    MeasurableSpace (FiniteAdeleRing (𝓞 K) K) :=
  borel _

instance borelSpace_finiteAdeleRing : BorelSpace (FiniteAdeleRing (𝓞 K) K) :=
  ⟨rfl⟩

noncomputable instance measurableSpace_adeleRing : MeasurableSpace 𝔸[K] :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance borelSpace_adeleRing : BorelSpace 𝔸[K] :=
  inferInstanceAs (BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

end GroundTheory.Global
