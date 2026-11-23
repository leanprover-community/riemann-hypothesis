module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

section Core

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

@[instance_reducible]
def coreComap (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    InnerProductSpace.Core ℂ V where
  inner x y := h.inner (f x) (f y)
  conj_inner_symm x y := h.conj_inner_symm (f x) (f y)
  re_inner_nonneg x := h.re_inner_nonneg (f x)
  add_left x y z := by simp only [map_add (f := _), h.add_left]
  smul_left x y r := by simp only [map_smul, h.smul_left]
  definite x hx := hf (by rw [map_zero]; exact h.definite _ hx)

theorem coreComap_inner (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W)
    (hf : Function.Injective f) (x y : V) :
    (coreComap h f hf).inner x y = h.inner (f x) (f y) := rfl

end Core

variable {K : Type*} [Field K]


variable (σ : K →+* ℂ) (E F : Type*) [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F]
  [Module (𝓞 K) F]

variable {σ E F}


variable [NumberField K]

variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]

end

end GroundTheory.Heights₂.Heights
