module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorLocal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry Order Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

theorem isNoetherian_of_finiteType {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] : IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  exact ⟨⟩

theorem isLocallyFactorial_of_dim_le_one {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (hX : topologicalKrullDim X ≤ 1) : IsLocallyFactorial X := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    change UniqueFactorizationMonoid X.functionField
    infer_instance
  · let Z : PrimeDivisor X := ⟨x, ringKrullDim_stalk_eq_one hX hx⟩
    have : IsDedekindDomain (X.presheaf.stalk x) := Z.isDedekindDomain_stalk
    have : IsPrincipalIdealRing (X.presheaf.stalk x) := by
      refine IsPrincipalIdealRing.of_finite_maximals ?_
      refine (Set.finite_singleton (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).subset ?_
      intro I hI
      exact IsLocalRing.eq_maximalIdeal hI
    infer_instance

end GroundTheory.Arith.SchemeCoh
