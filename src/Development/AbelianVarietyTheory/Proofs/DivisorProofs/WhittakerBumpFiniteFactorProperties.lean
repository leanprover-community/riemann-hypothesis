module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMemUpperUnipotent
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump.FinBump

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem psiFin_add (a b : Af E) : psiFin (a + b) = psiFin a * psiFin b := by
  simp only [psiFin, map_add (f := _), AddChar.map_add_eq_mul, Circle.coe_mul]

theorem bumpFin_eq (hK : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1)
    {g u : GL (Fin n) (Af E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hg : u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = psiFin (GlobalTheory.Whittaker.superDiag u) := by
  have h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n :=
    ⟨u, hu, hg⟩
  unfold bumpFin
  rw [dite_eq_left h]
  obtain ⟨hu', hg'⟩ := h.choose_spec
  set u' := h.choose
  have hw : u⁻¹ * u' ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) := mul_mem (inv_mem hu) hu'
  have hwK : u⁻¹ * u' ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
    have : u⁻¹ * u' = (u⁻¹ * g) * (u'⁻¹ * g)⁻¹ := by group
    rw [this]; exact mul_mem hg (inv_mem hg')
  have hsplit : u' = u * (u⁻¹ * u') := by group
  rw [hsplit, GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hw, psiFin_add, hK _ hw hwK, mul_one]

end GlobalTheory.WhitBump.FinBump

namespace GlobalTheory.WhitBump.FinBump

theorem bumpFin_zero_of_not {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {g : GL (Fin n) (Af E)}
    (h : ¬ ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = 0 := by
  unfold bumpFin; rw [dite_eq_right h]

theorem bumpFin_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) →
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  intro E _ _ _ n hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bumpFin_eq hK (one_mem _) (by simpa using one_mem _), hK 1 (one_mem _) (one_mem _)]
  · intro u hu g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : (u * v)⁻¹ * (u * g) = v⁻¹ * g := by group
      rw [bumpFin_eq hK (mul_mem hu hv) (by rw [e]; exact hvg), bumpFin_eq hK hv hvg,
        GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hv, psiFin_add]
    · rw [bumpFin_zero_of_not h, mul_zero]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, ?_⟩
      have e : (u⁻¹ * v)⁻¹ * g = v⁻¹ * (u * g) := by group
      rw [e]; exact hvg
  · intro k hk g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : v⁻¹ * (g * k) = (v⁻¹ * g) * k := by group
      rw [bumpFin_eq hK hv (by rw [e]; exact mul_mem hvg hk), bumpFin_eq hK hv hvg]
    · rw [bumpFin_zero_of_not h]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨v, hv, ?_⟩
      have e : v⁻¹ * g = (v⁻¹ * (g * k)) * k⁻¹ := by group
      rw [e]; exact mul_mem hvg (inv_mem hk)
  · intro g hg
    by_contra h
    exact hg (bumpFin_zero_of_not h)

end GlobalTheory.WhitBump.FinBump
