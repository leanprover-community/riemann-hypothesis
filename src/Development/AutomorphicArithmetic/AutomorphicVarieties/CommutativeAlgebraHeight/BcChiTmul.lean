module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem bc_D {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [inst : Algebra A S] [h : IsScalarTower A B S]
    (y : S ⊗[B] (B ⊗[A] E)) : (D.baseChange B).D S y = D.D S (Det.cancel A E B S y) := by
  have e : inst = ((algebraMap B S).comp (algebraMap A B)).toAlgebra :=
    Algebra.algebra_ext _ _ fun a => IsScalarTower.algebraMap_apply A B S a
  subst e
  rfl

private theorem cancel_one {A E : Type} [CommRing A] [Ring E] [Algebra A E] (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
    (y : B ⊗[A] E) : Det.cancel A E B S (1 ⊗ₜ y) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B S) (AlgHom.id A E) y := by
  induction y with
  | tmul b z => simp [Det.cancel_tmul]
  | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]

private theorem bc_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (y : B ⊗[A] E) : (D.baseChange B).chi y = D.chiS B y := by
  unfold Det.chi Det.chiS
  rw [bc_D, map_sub, cancel_one, Algebra.TensorProduct.one_def, Det.cancel_tmul, map_one, mul_one]

private theorem bc_chi_tmul {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (x : E) : (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) := by
  rw [bc_chi]
  have h := D.nat A[X] B[X] (Polynomial.mapAlgHom (Algebra.ofId A B)) (X ⊗ₜ 1 - 1 ⊗ₜ x)
  unfold Det.chi Det.chiS
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    simp
  · rfl

theorem UpperTheory.V.CA.d_bc :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type) [CommRing B] [Algebra A B], (∀ (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S] (y : S ⊗[B] (B ⊗[A] E)), (D.baseChange B).D S y = D.D S (Det.cancel A E B S y)) ∧ (∀ y, (D.baseChange B).val y = D.D B y) ∧ (∀ y, (D.baseChange B).chi y = D.chiS B y) ∧ ∀ x : E, (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) ∧ ∀ i, (D.baseChange B).lam i (1 ⊗ₜ x) = algebraMap A B (D.lam i x) := by
  intro n A E _ _ _ D B _ _
  refine ⟨fun S _ _ _ _ y => bc_D D B S y, fun y => ?_, bc_chi D B, fun x => ⟨bc_chi_tmul D B x, fun i => ?_⟩⟩
  · change (D.baseChange B).D B (1 ⊗ₜ y) = _
    rw [bc_D, cancel_one]
    congr 1
    induction y with
    | tmul b z => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · unfold Det.lam
    rw [bc_chi_tmul, Polynomial.coeff_map]
    simp
