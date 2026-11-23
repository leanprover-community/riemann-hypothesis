module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_mul_inv (V : HSp D) : HeisenbergWeilMatrices.gramA V * HeisenbergWeilMatrices.gramInvA V = 1 := by
  unfold HeisenbergWeilMatrices.gramA HeisenbergWeilMatrices.gramInvA
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inv_mul_gram (V : HSp D) : HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V = 1 := mul_eq_one_comm.1 (gram_mul_inv V)

def kap (A B : HSp D) : WA A B ≃+ WA A B where
  toFun x := HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x
  invFun y := HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ y
  left_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, inv_mul_gram, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, gram_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _

theorem kap_symm_apply (A B : HSp D) (x : WA A B) : (kap A B).symm x = HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ x := rfl

def kapT (A B : HSp D) : WA A B ≃+ WA B A := (kap A B).trans (Matrix.transposeAddEquiv _ _ _)

def IsChange {A B V W : HSp D} (κ : WA A B ≃+ WA V W) (σ : GA D V × GA D W → GA D A × GA D B) : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ x y, symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp x y) ∧
    (∀ x, κ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B) ∧ (∀ (c : AE D) x, κ (c • x) = c • κ x) ∧
    ∀ g h x, actHom V W g h (κ x) = κ (HeisenbergWeilMatrices.act (σ (g, h)) x)

end GlobalTheory.WeilTieCompare

end
