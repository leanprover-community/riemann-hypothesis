module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
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
import GroundTheory.AutomorphicForms.GL2.GodementSection
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRankOne

theorem weakFEPair_Λ₀_of_smul (P Q : WeakFEPair ℂ) (c : ℂ) (hf : Q.f = c • P.f)
    (hg : Q.g = c • P.g) (hk : Q.k = P.k) (hε : Q.ε = P.ε) (hf₀ : Q.f₀ = c • P.f₀)
    (hg₀ : Q.g₀ = c • P.g₀) : Q.Λ₀ = c • P.Λ₀ := by
  have hmod : Q.f_modif = c • P.f_modif := by
    funext x
    simp only [WeakFEPair.f_modif, Pi.add_apply, Pi.smul_apply, Set.indicator_apply, hf, hf₀, hg₀, hk, hε,
      smul_eq_mul]
    split_ifs <;> ring
  funext s
  simp only [WeakFEPair.Λ₀, hmod, Pi.smul_apply]
  exact mellin_const_smul P.f_modif s c

end GlobalTheory.CompanionTheory.EisRankOne
