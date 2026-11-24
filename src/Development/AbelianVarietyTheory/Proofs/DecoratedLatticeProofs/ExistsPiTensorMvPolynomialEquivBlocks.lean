module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.BlockPoly

variable (ι σ : Type) [Fintype ι] [DecidableEq ι]

noncomputable def blockMul :
    (ι → MvPolynomial σ ℂ) →ₘₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap)

theorem blockMul_apply (f : ι → MvPolynomial σ ℂ) :
    blockMul ι σ f = ∏ τ, rename (Prod.mk τ) (f τ) := by
  simp [blockMul]

noncomputable def expEquiv : (ι → σ →₀ ℕ) ≃ (ι × σ →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.trans Finsupp.curryEquiv.symm

theorem expEquiv_apply (d : ι → σ →₀ ℕ) (a : ι) (b : σ) : expEquiv ι σ d (a, b) = d a b := by
  simp [expEquiv]

theorem sum_mapDomain_eq (d : ι → σ →₀ ℕ) :
    ∑ τ, (d τ).mapDomain (Prod.mk τ) = expEquiv ι σ d := by
  ext ⟨a, b⟩
  rw [expEquiv_apply, Finset.sum_apply', Finset.sum_eq_single a]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => by simpa using h) _ _
  · intro τ _ hτ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨c, hc⟩
    exact hτ (congrArg Prod.fst hc)
  · intro h; exact absurd (Finset.mem_univ a) h

theorem prod_rename_monomial (d : ι → σ →₀ ℕ) :
    ∏ τ, rename (Prod.mk τ) (monomial (d τ) (1 : ℂ)) = monomial (expEquiv ι σ d) 1 := by
  simp only [rename_monomial]
  rw [← monomial_sum_one, sum_mapDomain_eq]

noncomputable def blockEquiv :
    PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).equiv
    (basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

theorem blockEquiv_toLinearMap :
    (blockEquiv ι σ).toLinearMap = PiTensorProduct.lift (blockMul ι σ) := by
  refine (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).ext (fun p => ?_)
  rw [LinearEquiv.coe_coe, blockEquiv, Module.Basis.equiv_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.lift.tprod, blockMul_apply]
  simp only [coe_basisMonomials]
  rw [prod_rename_monomial]

theorem blockEquiv_tprod (f : ι → MvPolynomial σ ℂ) :
    blockEquiv ι σ (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  rw [← LinearEquiv.coe_coe, blockEquiv_toLinearMap, PiTensorProduct.lift.tprod, blockMul_apply]

theorem map_subtype_injective (U : ι → Submodule ℂ (MvPolynomial σ ℂ)) :
    Function.Injective (PiTensorProduct.map fun τ => (U τ).subtype) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective (U τ).subtype (U τ).ker_subtype
  have h : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) =
      LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  exact Function.LeftInverse.injective (g := PiTensorProduct.map g)
    (fun x => by simpa using LinearMap.congr_fun h x)

theorem exists_blockEquiv :
    ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  intro ι σ _ _
  refine ⟨blockEquiv ι σ, blockEquiv_tprod ι σ, fun U => ⟨?_, ?_⟩⟩
  · exact (blockEquiv ι σ).injective.comp (map_subtype_injective ι σ U)
  · rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨fun τ => (g τ : MvPolynomial σ ℂ), fun τ => (g τ).2, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (fun τ => (⟨f τ, hf τ⟩ : U τ)), ⟨_, rfl⟩, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]

end GlobalTheory.BlockPoly
