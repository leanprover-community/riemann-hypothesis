module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Mathlib.RingTheory.GradedAlgebra.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

private theorem gr_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) :
    GrMat 𝒜 (X * Y) := by
  intro a b
  simp only [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by simp only [wt]; ring
  rwa [e] at h

private theorem gr_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := by
  intro a b
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq]
    have e : wt a a = 0 := by simp [wt]
    rw [e]
    exact SetLike.GradedOne.one_mem
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

private theorem gr_pow {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) (n : ℕ) :
    GrMat 𝒜 ((g ^ n : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  induction n with
  | zero => rw [pow_zero]; exact gr_one 𝒜
  | succ n ih => rw [pow_succ, Units.val_mul]; exact gr_mul 𝒜 ih hg

private theorem gr_inv [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  have hn := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact gr_pow 𝒜 hg _

private theorem gr_theta [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [theta_val]
  have hi := gr_inv 𝒜 hg
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three, Fin.rev]
  intro a b
  rw [key]
  have e : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
  rw [← e]
  exact hi _ _

private theorem gr_act [Finite R] (s : ℤˣ) {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one]; exact hg
  · rw [sgnAct_neg_one]; exact gr_theta 𝒜 hg

end

theorem UpperTheory.graded_matrix_mul_inv :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (x y : GG (m := 3) (R := R)),
      GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y).mat ∧ GrMat 𝒜 (x⁻¹).mat := by
  intro O R _ _ _ _ 𝒜 _ x y hx hy
  unfold GG.mat at *
  constructor
  · rw [SemidirectProduct.mul_left, Units.val_mul]
    exact gr_mul 𝒜 hx (gr_act 𝒜 _ hy)
  · rw [SemidirectProduct.inv_left]
    exact gr_act 𝒜 _ (gr_inv 𝒜 hx)
