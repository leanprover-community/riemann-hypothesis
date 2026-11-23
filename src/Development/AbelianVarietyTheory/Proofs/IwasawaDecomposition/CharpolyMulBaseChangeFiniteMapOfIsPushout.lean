module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.Ring.Constructions

@[expose] public section

noncomputable section

namespace GlobalTheory.NormalDescent

open CategoryTheory Polynomial TensorProduct

theorem charK_map_of_isPushout {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Field K] [Field K'] [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B')
    (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K')
    (hι : ∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) (b : B) :
    charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  haveI : Module.Finite A B := hφ
  haveI : Module.Finite A' B' := hφ'
  letI : Algebra K K' := ι.toAlgebra
  letI : Algebra A K' := (ι.comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => hι a
  let e : K' ⊗[K] (K ⊗[A] B) ≃ₗ[K'] K' ⊗[A'] B' :=
    AlgebraTensorModule.cancelBaseChange A K K' K' B ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A A' K' K' B).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl K' K') hb.equiv
  unfold charK
  change (Algebra.lmul K' (K' ⊗[A'] B') (1 ⊗ₜ β b)).charpoly =
    (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly.map (algebraMap K K')
  rw [← LinearMap.charpoly_baseChange, ← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add (f := _), hs, ht]
  | tmul c' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [tmul_add, map_add (f := _), hs, ht]
    | tmul c x =>
      simp [e, IsBaseChange.equiv_tmul]
      rfl

end GlobalTheory.NormalDescent
