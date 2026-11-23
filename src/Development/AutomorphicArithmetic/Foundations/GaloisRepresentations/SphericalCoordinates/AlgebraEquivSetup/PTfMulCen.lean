module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem UpperTheory.Gal.W2.Seed.tf_mul_cen_apply {X M : Type} [Group X] [Group M] (T : TyLev X M)
    (h z : X) (hz : T.Cen z) (g : X) : T.tf (h * z) g = T.tf h (z⁻¹ * g) := by
  have hzc := hz.1
  have hpr : T.L.pr (z⁻¹ * g) = T.L.pr g := by
    rw [map_mul, map_inv, hz.2, inv_one, one_mul]
  have key : ∀ a b : X, a * (h * z) * b = z * (a * h * b) := by
    intro a b
    calc a * (h * z) * b = a * h * (z * b) := by group
      _ = a * h * (b * z) := by rw [hzc b]
      _ = (a * h * b) * z := by group
      _ = z * (a * h * b) := (hzc _).symm
  have hmem : g ∈ DoubleCoset.doubleCoset (h * z) (T.K : Set X) T.K ↔
      z⁻¹ * g ∈ DoubleCoset.doubleCoset h (T.K : Set X) T.K := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [key]; group⟩
    · rintro ⟨a, ha, b, hb, he⟩
      refine ⟨a, ha, b, hb, ?_⟩
      rw [key, ← he]
      group
  simp only [TyLev.tf, dosetInd, hpr, Set.indicator_apply, hmem, Pi.one_apply]

theorem UpperTheory.Gal.W2.Seed.pTfMulCen :
    TfAdm → TfCen → TfIdem → TfMulCen := by
  intro hAdm hCen hIdem X M _ _ T h z hh hz
  have hzc : ∀ y : X, z⁻¹ * y = y * z⁻¹ := fun y => (Commute.inv_left (hz.1 y : Commute z y)).eq
  refine ⟨?_, ?_⟩
  · funext g
    have hty : T.IsTy (V := ℂ) (fun y : X => T.tf h (y⁻¹ * g)) := by
      intro k hk y
      have e := ((hAdm X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1
      simp only [mul_inv_rev, mul_assoc]
      rw [e]
      simp only [map_inv, smul_eq_mul]
      congr 1
      rw [← map_inv]
      exact congrArg (fun u => ((T.ψ u : ℂˣ) : ℂ)) (Subtype.ext (inv_inv _))
    have e := hCen X M T z hz ℂ (fun y => T.tf h (y⁻¹ * g)) hty 1
    simp only [hAct, one_mul, smul_eq_mul] at e
    simp only [conv]
    rw [e, tf_mul_cen_apply T h z hz g]
  · funext g
    have e1 : conv T.K₀ (T.tf h) (T.tf z) g = conv T.K₀ (T.tf h) (T.tf 1) (z⁻¹ * g) := by
      simp only [conv]
      refine finsum_congr fun x => ?_
      congr 1
      have e := tf_mul_cen_apply T 1 z hz (x.out⁻¹ * g)
      rw [one_mul] at e
      rw [e, ← mul_assoc, ← mul_assoc, hzc]
    rw [e1, (hIdem X M T h hh).2.1, tf_mul_cen_apply T h z hz g]
