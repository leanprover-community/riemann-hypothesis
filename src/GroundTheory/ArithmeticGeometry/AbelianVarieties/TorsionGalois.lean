module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Galois.Notation
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.ProfiniteCohomology.DiscreteModules
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

namespace GroundTheory.Arith.Abelian

open GroundTheory.ProfCoh IntermediateField AddSubgroup WeierstrassCurve

universe w u

section Action

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)

noncomputable def galPointsHom : Gal(L/K) →* AddMonoid.End (W.baseChange L).toAffine.Point where
  toFun σ := Affine.Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)
  map_one' := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl

theorem galPointsHom_some (σ : Gal(L/K)) {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange L).toAffine.Nonsingular (σ x) (σ y),
      galPointsHom K L W σ (.some x y h) = .some (σ x) (σ y) h' :=
  ⟨_, rfl⟩

theorem galPointsHom_some_eq_self {σ : Gal(L/K)} {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) (hx : σ x = x) (hy : σ y = y) :
    galPointsHom K L W σ (.some x y h) = .some x y h := by
  obtain ⟨h', e⟩ := galPointsHom_some K L W σ h
  rw [e]
  simp only [Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

end Action

section Discrete

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)

variable [Algebra.IsIntegral K L]

end Discrete

section SepClosed

instance isElliptic_baseChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] [IsSepClosed L]
  (W : WeierstrassCurve K) [W.IsElliptic]

end SepClosed

end GroundTheory.Arith.Abelian
