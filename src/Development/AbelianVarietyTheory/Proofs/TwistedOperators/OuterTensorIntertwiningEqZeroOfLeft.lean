module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Intertwining
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
public import Formalism.RealPlaceAnalysis.FockPairGl
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_contract_right {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (z : V ⊗[ℂ] W)
    (h : ∀ l : Module.Dual ℂ W, TensorProduct.rid ℂ V (LinearMap.lTensor V l z) = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  simp [TensorProduct.equivFinsuppOfBasisRight_apply, h]

theorem outerTensor_intertwining_eq_zero_of_left :
    ∀ (G H V W V' W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (ρ' : Representation ℂ G V') (σ' : Representation ℂ H W'), (∀ ψ : ρ.IntertwiningMap ρ', ψ = 0) → ∀ φ : (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IntertwiningMap (Representation.tprod (ρ'.comp (MonoidHom.fst G H)) (σ'.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V' ⊗[ℂ] W')), φ = 0 := by
  intro G H V W V' W' _ _ _ _ _ _ _ _ _ _ ρ σ ρ' σ' h φ

  have hpure : ∀ (v : V) (w : W), φ (v ⊗ₜ[ℂ] w) = 0 := by
    intro v w
    apply tensor_eq_zero_of_forall_contract_right
    intro l
    let f : V →ₗ[ℂ] V' :=
      (TensorProduct.rid ℂ V').toLinearMap ∘ₗ LinearMap.lTensor V' l ∘ₗ φ.toLinearMap ∘ₗ
        (TensorProduct.mk ℂ V W).flip w
    have hf : ∀ (g : G) (x : V), f (ρ g x) = ρ' g (f x) := by
      intro g x
      have key : ∀ y : V' ⊗[ℂ] W', TensorProduct.rid ℂ V'
          (LinearMap.lTensor V' l (TensorProduct.map (ρ' g) (σ' 1) y)) =
          ρ' g (TensorProduct.rid ℂ V' (LinearMap.lTensor V' l y)) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a c => simp
        | add a c ha hc => simp only [map_add (f := _), ha, hc]
      have e1 : ρ g x ⊗ₜ[ℂ] w = (Representation.tprod (ρ.comp (MonoidHom.fst G H))
          (σ.comp (MonoidHom.snd G H))) (g, 1) (x ⊗ₜ[ℂ] w) := by
        simp [Representation.tprod_apply]
      have e2 := Representation.IntertwiningMap.isIntertwining _ _ φ (g, 1) (x ⊗ₜ[ℂ] w)
      simp only [f, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        Representation.IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe]
      rw [e1, e2, Representation.tprod_apply]
      exact key _
    have h0 := h (f.intertwiningMap_of_isIntertwiningMap ρ ρ' hf)
    have hv := congrArg (fun ψ : ρ.IntertwiningMap ρ' => ψ v) h0
    simpa [f] using hv
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v w
  simp [hpure]

end GlobalTheory
