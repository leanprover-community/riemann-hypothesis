module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2.NCov

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {S : Set (End K V)} [IsLocalRing O]

end Formalism.L2.NCov

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def SplitEx (D : D7) : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

end Formalism.L2
