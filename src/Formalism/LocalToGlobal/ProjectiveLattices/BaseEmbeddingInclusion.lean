module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
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
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

end Forms

end Formalism.L2.Pj
