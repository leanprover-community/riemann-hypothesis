module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsBC_of :
    SplitsBC := by
  intro R R' S B _ _ _ _ _ _ _ _ _ I z hz
  let z' : I → (R' ⊗[R] S →ₐ[R'] B) := fun i =>
    Algebra.TensorProduct.lift (Algebra.ofId R' B) (z i) (fun _ _ => Commute.all _ _)
  have hz' : ∀ i (r : R') (s : S), z' i (r ⊗ₜ s) = algebraMap R' B r * z i s := by
    intro i r s
    simp [z', Algebra.ofId_apply]
  refine ⟨z', ?_, ?_⟩
  · have key : ∀ x, splitMap z' x =
        splitMap z (Algebra.TensorProduct.cancelBaseChange R R' B B S x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul b y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [tmul_add, map_add (f := _), ha, hc]
        | tmul r s =>
          funext i
          rw [splitMap_tmul, hz', Algebra.TensorProduct.cancelBaseChange_tmul, splitMap_tmul]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    have hfun : (⇑(splitMap z') : B ⊗[R'] (R' ⊗[R] S) → (I → B)) =
        (splitMap z) ∘ (Algebra.TensorProduct.cancelBaseChange R R' B B S) := funext key
    unfold Splits
    rw [hfun]
    exact hz.comp (AlgEquiv.bijective _)
  · intro i s
    rw [hz']
    simp
