module

public import Formalism.LocalRingCardinality.DataArith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.ProvRowSide

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def stdHLat (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := L

theorem stdHLat_frames (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K) :
    IsUnit ((stdHLat K n L).X v).det := by
  show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
  simp

variable {K}

def coordMap (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W) :
    (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

set_option linter.unusedSectionVars false in
theorem coordMap_basisFun (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W)
    (i : Fin n) : coordMap e c (Pi.basisFun K (Fin n) i) = c i := by
  simp [coordMap, Pi.single_apply, apply_ite e, ite_smul]

theorem normAt_one (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (c : OrthonormalBasis (Fin n) ℂ W) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (fun _ => 1) (InfinitePlace.mk e) x = ‖coordMap e c x‖ := by
  have h1 : coordMap e c x = c.repr.symm (WithLp.toLp 2 (fun i => e (x i))) := by
    rw [← c.sum_repr_symm]; rfl
  rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  simp [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

end Std

section WithRRDef

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

end WithRRDef

section Small

variable (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  {n : ℕ} (c : OrthonormalBasis (Fin n) ℂ EE)

end Small

end GlobalTheory.ProvRowSide

end
