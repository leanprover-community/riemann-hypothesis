module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem

@[expose] public section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.card_dual_residueField_eq_card_of_maximalIdeal_smul_eq_zero :
    ∀ {O N : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [AddCommGroup N] [Module O N] [Finite N], (∀ a ∈ maximalIdeal O, ∀ x : N, a • x = 0) → Nat.card (N →ₗ[O] ResidueField O) = Nat.card N := by
  intro O N _ _ _ _ _ _ h
  classical
  have hM : Module.IsTorsionBySet O N (maximalIdeal O) := fun x a => h a a.2 x
  letI : Module (ResidueField O) N := hM.module
  haveI : IsScalarTower O (ResidueField O) N := hM.isScalarTower
  have e := LinearMap.extendScalarsOfSurjectiveEquiv (R := O) (S := ResidueField O) (M := N)
    (N := ResidueField O) IsLocalRing.residue_surjective
  rw [Nat.card_congr e.toEquiv]
  let b := Module.Free.chooseBasis (ResidueField O) N
  exact (Nat.card_congr b.toDualEquiv.toEquiv).symm
