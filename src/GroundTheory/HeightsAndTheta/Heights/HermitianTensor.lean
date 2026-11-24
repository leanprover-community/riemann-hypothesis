module

public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section SMul

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

theorem fibre_smul_eq (a : ComplexAt σ) (x : Fibre σ E) :
    a • x = (ofComplex σ).symm a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | tmul z e => rw [smul_tmul', smul_tmul', complex_smul_def, smul_eq_mul]; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

end SMul

variable [NumberField K]

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

def FibreSpace (_h : HermitianMetric K E) (σ : K →+* ℂ) : Type _ := Fibre σ E

namespace FibreSpace

variable (h : HermitianMetric K E) (σ : K →+* ℂ)

instance : AddCommGroup (FibreSpace h σ) := inferInstanceAs (AddCommGroup (Fibre σ E))

instance : Module ℂ (FibreSpace h σ) := inferInstanceAs (Module ℂ (Fibre σ E))

instance : NormedAddCommGroup (FibreSpace h σ) :=
  letI : InnerProductSpace.Core ℂ (FibreSpace h σ) := h.form σ
  this.toNormedAddCommGroup

instance : InnerProductSpace ℂ (FibreSpace h σ) := InnerProductSpace.ofCore _

def equiv : Fibre σ E ≃ₗ[ℂ] FibreSpace h σ := LinearEquiv.refl ℂ _

theorem inner_equiv (x y : Fibre σ E) :
    inner ℂ (equiv h σ x) (equiv h σ y) = (h.form σ).inner x y := rfl

end FibreSpace

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]

variable (hE : HermitianMetric K E) (hF : HermitianMetric K F)

end

end GroundTheory.Heights₂.Heights
