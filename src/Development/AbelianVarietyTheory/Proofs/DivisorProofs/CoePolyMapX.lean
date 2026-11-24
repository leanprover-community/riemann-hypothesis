module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def rightInc (A : Subalgebra ℂ K) : κ' →+* tens (κ' := κ') A :=
  (Algebra.TensorProduct.includeRight : κ' →ₐ[ℂ] K ⊗[ℂ] κ').toRingHom.codRestrict
    (tens (κ' := κ') A).toSubring fun b => tmul_mem (one_mem A) b

def polyMap (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) :
    MvPolynomial (Fin m) κ' →+* tens (κ' := κ') A :=
  MvPolynomial.eval₂Hom (rightInc A) fun i => ⟨(v i : K) ⊗ₜ 1, tmul_mem (v i).2 1⟩

@[simp] theorem coe_polyMap_X (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (i : Fin m) :
    (polyMap (κ' := κ') A v (MvPolynomial.X i) : K ⊗[ℂ] κ') = (v i : K) ⊗ₜ 1 := by
  simp [polyMap]

@[simp] theorem coe_polyMap_C (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (b : κ') :
    (polyMap (κ' := κ') A v (MvPolynomial.C b) : K ⊗[ℂ] κ') = 1 ⊗ₜ b := by
  simp [polyMap, rightInc]

end GlobalTheory.GraphLocal
