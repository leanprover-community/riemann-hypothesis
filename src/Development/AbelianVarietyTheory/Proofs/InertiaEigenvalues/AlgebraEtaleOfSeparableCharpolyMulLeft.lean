module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem etale_of_separable_charpoly_mulLeft (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (h : (LinearMap.mulLeft E g).charpoly.Separable) :
    Algebra.Etale E A := by
  have hd := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable (LinearMap.mulLeft E g) h
  have h2 : minpoly E (LinearMap.mulLeft E g) = minpoly E g :=
    minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective) g
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm : (minpoly E g).Monic := minpoly.monic hint
  have hd' : minpoly E g ∣ (LinearMap.mulLeft E g).charpoly := by
    rw [← h2]; exact LinearMap.minpoly_dvd_charpoly _
  rw [h2] at hd
  have heq : minpoly E g = (LinearMap.mulLeft E g).charpoly :=
    eq_of_monic_of_associated hm (LinearMap.charpoly_monic _) (associated_of_dvd_dvd hd' hd)
  have hsep : (minpoly E g).Separable := heq ▸ h
  have hdeg : (minpoly E g).natDegree = Module.finrank E A := by
    rw [heq, LinearMap.charpoly_natDegree]
  haveI : Module.Finite E (AdjoinRoot (minpoly E g)) := hm.finite_adjoinRoot
  let φ : AdjoinRoot (minpoly E g) →ₐ[E] A := AdjoinRoot.liftAlgHom (minpoly E g) (Algebra.ofId E A) g (minpoly.aeval E g)
  have hli : LinearIndependent E fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ) :=
    linearIndependent_pow g
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp [hdeg])
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨AdjoinRoot.root (minpoly E g) ^ (i : ℕ), ?_⟩
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', AlgHom.toLinearMap_apply, map_pow]
    congr 1
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hfr : Module.finrank E (AdjoinRoot (minpoly E g)) = Module.finrank E A := by
    rw [(AdjoinRoot.powerBasis' hm).finrank]; simpa using hdeg
  have hinj : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
  let e : AdjoinRoot (minpoly E g) ≃ₐ[E] A := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hu : IsUnit (AdjoinRoot.mk (minpoly E g) (minpoly E g).derivative) := by
    obtain ⟨a, c, hac⟩ := hsep
    have := congrArg (AdjoinRoot.mk (minpoly E g)) hac
    rw [map_add (f := _), map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact this⟩
  have := GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hm hu
  exact Algebra.Etale.of_equiv e

end GlobalTheory
