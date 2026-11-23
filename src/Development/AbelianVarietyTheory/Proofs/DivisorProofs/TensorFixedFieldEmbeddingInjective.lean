module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.BaseChangeCent

variable {p : ℕ} [Fact p.Prime]

def shL (G : HTGroup p) : G.C →ₗ[ℚ] G.C where
  toFun := sh G
  map_add' x y := by simp only [sh, map_add (f := _), MulOpposite.unop_add]
  map_smul' q x := by
    show (G.star (q • x)).unop = q • (G.star x).unop
    rw [map_rat_smul]; rfl

theorem shL_apply (G : HTGroup p) (c : G.C) : shL G c = sh G c := rfl

def phi (G : HTGroup p) (β Y : G.C) (β' : G.C) : G.C →ₗ[ℚ] G.C × G.C :=
  (LinearMap.mulRight ℚ Y - LinearMap.mulLeft ℚ Y).prod
    (LinearMap.mulLeft ℚ β ∘ₗ LinearMap.mulRight ℚ β' ∘ₗ shL G - LinearMap.id)

theorem phi_apply (G : HTGroup p) (β Y β' c : G.C) :
    phi G β Y β' c = (c * Y - Y * c, β * sh G c * β' - c) := by
  simp [phi, shL_apply, mul_assoc]

theorem lTensor_phi (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (β Y β' : G.C)
    (x : K ⊗[ℚ] G.C) :
    TensorProduct.prodRight ℚ ℚ K G.C G.C ((phi G β Y β').lTensor K x) =
      (x * inC G K Y - inC G K Y * x, inC G K β * (starT G.star K x).unop * inC G K β' - x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul k c =>
    simp only [LinearMap.lTensor_tmul, phi_apply, TensorProduct.prodRight_tmul, inC, starT_tmul,
      AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_sub, sh]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy]
    simp only [map_add (f := _), MulOpposite.unop_add, mul_add, add_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> abel

end GlobalTheory.FinClsLoc.BaseChangeCent
