module

public import Mathlib.LinearAlgebra.Transvection.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace GlobalTheory

open Module

section Defs

variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

def isoTransvection (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) : M ≃ₗ[R] M :=
  LinearEquiv.transvection (f := b • h.flip x) (v := x) (by simp [hx])

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

theorem apply (b : R) (v : M) : isoTransvection h x hx b v = v + (b * h v x) • x := rfl

end isoTransvection

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

variable {h}

variable (h)


variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]


end isoTransvection

end Defs


namespace isoTransvection

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)

end isoTransvection

namespace isoTransvection

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x : W)
  (hx : h x x = 0)

end isoTransvection


section Example

private noncomputable def hyp : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u v => u.1 * star v.2 + u.2 * star v.1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

end Example

end GlobalTheory
