module

public import Formalism.FockGram.StatementLat
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

open Matrix Module

namespace Formalism.E

theorem indexEqNormDet : SubIndexNorm := by
  intro S M ι _ _ _ _ _ _ _ b N bN
  classical
  haveI : Module.Free S M := Module.Free.of_basis b
  haveI : Module.Finite S M := Module.Finite.of_basis b
  haveI : Module.Free ℤ M := Module.Free.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  haveI : Module.Finite ℤ M := Module.Finite.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  let e0 : M ≃ₗ[S] N := b.equiv bN (Equiv.refl ι)
  let f : M →ₗ[S] M := N.subtype ∘ₗ e0.toLinearMap
  have hS : b.det (fun i => (bN i : M)) = LinearMap.det f := by
    rw [Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext x y
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [f, e0]
  let N' : Submodule ℤ M := N.restrictScalars ℤ
  let e : M ≃ₗ[ℤ] N' := (e0.trans (Submodule.restrictScalarsEquiv ℤ S M N).symm).restrictScalars ℤ
  have h1 := Submodule.natAbs_det_equiv N' e
  have hcard : Nat.card (M ⧸ N') = Nat.card (M ⧸ N) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ N).toEquiv
  rw [← hcard, ← h1, hS, ← LinearMap.det_restrictScalars]
  congr 2

end Formalism.E
