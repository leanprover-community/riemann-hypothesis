module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

open scoped nonZeroDivisors

theorem GlobalTheory.UCls.selfDual_latOf_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  intro E _ _ _ r G Λ g0 hΛ hua
  obtain ⟨hG, hdet, hfg, hspan, hsd⟩ := hΛ
  obtain ⟨hunit, hpres⟩ := hua
  let g : GL (Fin r) (RA (maximalRealSubfield E) E) := Matrix.nonsingInvUnit g0 hunit
  have hg : (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) = g0 := rfl
  obtain ⟨L, hL, hLfg, hLspan, hLhat⟩ :=
    GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E r Λ g hfg hspan
  rw [hg] at hL hLhat
  have hmem : ∀ x : E, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ x := by
    intro x
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.isIntegral_coe
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsd' : ∀ v : Fin r → E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * G a b * (IsCMField.complexConj E) (y b)) ∈
      (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔ v ∈ Λ := by
    intro v
    simp only [hmem]
    exact hsd v
  have key := GlobalTheory.AdLat.latOf_selfDual (maximalRealSubfield E) E r Λ (IsCMField.complexConj E) G 1 g
    hfg hspan (IsCMField.complexConj_apply_apply E) hG hdet one_ne_zero hsd' (by rw [hg]; exact hpres)
  rw [hg] at key
  refine ⟨L, hL, hLhat, hG, hdet, hLfg, hLspan, fun x => ?_⟩
  have := key x
  rw [← hL] at this
  simp only [hmem, SetLike.mem_coe] at this
  exact this
