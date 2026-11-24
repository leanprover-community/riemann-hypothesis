module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
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

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_smul {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L) :
    T c k hk f (a • z) = c a * T c k hk f z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul b y =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]

end GlobalTheory.CompanionTheory.FrobPairing
