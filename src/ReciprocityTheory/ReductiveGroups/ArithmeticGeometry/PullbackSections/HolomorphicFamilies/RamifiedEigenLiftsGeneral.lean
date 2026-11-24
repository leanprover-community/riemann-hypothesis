module

public import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamData
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBIdemDen
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB Pf.ERam

theorem dual_int {E : Type} [Field E] [NumberField E] (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) :
    ∀ i : Fin (nI E), IsIntegral ℤ ((δ : E) * omDF (E := E) i) := by
  set ω := RingOfIntegers.basis E
  set bq := integralBasis E
  have hbqω : ∀ i, bq i = algebraMap (𝓞 E) E (ω i) := fun i => integralBasis_apply E i
  have h := _root_.PI.UnitaryGroupMassFormula.TBIdemDen.dualDiff E _ bq (fun i => by rw [hbqω]; exact RingOfIntegers.isIntegral_coe _) (fun x => by
      refine ⟨fun i => ω.repr x i, ?_⟩
      have h1 := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)

      rw [map_sum] at h1
      show algebraMap (𝓞 E) E x = _
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbqω, map_zsmul, Int.cast_smul_eq_zsmul]) _ hδ
  intro i
  exact h _

end ReciprocityTheory.ChartRestriction.G.PullbackSections
