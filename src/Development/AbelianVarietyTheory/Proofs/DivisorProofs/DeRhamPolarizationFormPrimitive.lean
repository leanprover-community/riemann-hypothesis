module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeWeil

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  have := hA.comm
  have h := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [CechPic.cls_linComb hL _ _ _, Fin.sum_univ_eight] at e
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [CechPic.cls_linComb hL _ _ _, ← e, ← Equiv.ulift.symm.sum_comp]
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {{0, 1, 2}, {0, 1}, {0, 2}, {1, 2}, {0}, {1}, {2}, ∅} := by
    decide
  rw [u]
  iterate 7 rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have k0 : psum A (x3 A) {0, 1, 2} = x3 A 0 * x3 A 1 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 1 * (x3 A 2 * 1)) from rfl).trans (by rw [_root_.mul_one, _root_.mul_assoc])
  have k1 : psum A (x3 A) {0, 1} = x3 A 0 * x3 A 1 :=
    (show _ = x3 A 0 * (x3 A 1 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k2 : psum A (x3 A) {0, 2} = x3 A 0 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k3 : psum A (x3 A) {1, 2} = x3 A 1 * x3 A 2 :=
    (show _ = x3 A 1 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k4 : psum A (x3 A) {0} = x3 A 0 := _root_.mul_one (x3 A 0)
  have k5 : psum A (x3 A) {1} = x3 A 1 := _root_.mul_one (x3 A 1)
  have k6 : psum A (x3 A) {2} = x3 A 2 := _root_.mul_one (x3 A 2)
  have k7 : psum A (x3 A) ∅ = 1 := rfl
  simp only [Equiv.ulift_symm_down, k0, k1, k2, k3, k4, k5, k6, k7, ← add_assoc]
  rfl

section Point

variable {R D : Type} [CommRing R] [CommRing D] [Bialgebra R D] [Module.Finite R D] [Module.Projective R D]
  [Coalgebra.IsCocomm R D]

end Point

section Tower

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {𝒜 ℬ : PDivGroup p R}

end Tower

section Linear

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {𝒜 : PDivGroup p K}
  {w : 𝒜 ⟶ 𝒜.dual} {E : V ≃ₗ[K] 𝒜.RigExt} {β : V →ₗ[K] V →ₗ[K] K} {ε : ℤˣ}


end Linear

end GlobalTheory.HodgeWeil
