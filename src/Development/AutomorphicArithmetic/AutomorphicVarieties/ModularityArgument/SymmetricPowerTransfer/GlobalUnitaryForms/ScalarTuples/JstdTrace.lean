module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DOrb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem jstd_trace {K : Type} [Field K] (τ : K) : (jstd τ ω).trace = τ := by
  simp [jstd, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun]

private theorem toUnit_val {R : Type} [Monoid R] {x : R} (h : IsUnit x) : ((toUnit x : Rˣ) : R) = x := by
  simp [toUnit, h]

private theorem omega_unit {K : Type} [Field K] (τ : K) : IsUnit (ω : Etau K τ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by simp [QuadraticAlgebra.norm_def])

theorem UpperTheory.V.Z.Sym.Glob.locD :
    UpperTheory.V.Z.Sym.Glob.LocD := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j hγ hj χ hχ z hz
  obtain ⟨j', hj'tr, hS, hK⟩ := dOrb O K Δ τ L hτ γ j hγ hj
  have hc := gConj O K Δ τ L hτ j' (jstd τ) hj'tr (jstd_trace τ)
  have hunr1 : Unr O (1 : Kˣ →* ℂˣ) := fun u => rfl
  have hzu : toUnit (1 + ω : Etau K τ) = z := by
    apply Units.ext
    rw [toUnit_val (by rw [← hz]; exact z.isUnit), hz]
  refine ⟨?_, ?_⟩
  · rw [← hc.2 1 hunr1]
    exact hS _ (toUnit_val (omega_unit τ))
  · rw [hzu, ← hc.2 χ hχ]
    exact hK χ hχ z
