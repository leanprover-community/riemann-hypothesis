module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.BilinearMap
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Defs

@[expose] public section

namespace KStar.Cstarloc

structure UnramDatum (R : Type*) [CommRing R] [StarRing R] : Prop where
  trace_one : ∃ e : R, e + star e = 1
  norm_onto : ∀ u : R, IsUnit u → star u = u → ∃ a : R, a * star a = u

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

abbrev Sesq (R : Type*) [CommRing R] [StarRing R] (M : Type*) [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R

def IsHerm (h : Sesq R M) : Prop := ∀ x y, h y x = star (h x y)

def IsUnimod (h : Sesq R M) : Prop := Function.Bijective (h.flip : M → Module.Dual R M)

def gram {ι : Type*} (h : Sesq R M) (b : ι → M) : Matrix ι ι R := Matrix.of fun i j => h (b i) (b j)

def IsOrthonormal {ι : Type*} [DecidableEq ι] (h : Sesq R M) (b : ι → M) : Prop := gram h b = 1

def perp (h : Sesq R M) (x : M) : Submodule R M := LinearMap.ker (h.flip x)

def restr (h : Sesq R M) (N : Submodule R M) : Sesq R N := h.domRestrict₁₂ N N

theorem mem_perp (h : Sesq R M) (x y : M) : y ∈ perp h x ↔ h y x = 0 := by
  rw [perp, LinearMap.mem_ker, LinearMap.flip_apply]

end KStar.Cstarloc
