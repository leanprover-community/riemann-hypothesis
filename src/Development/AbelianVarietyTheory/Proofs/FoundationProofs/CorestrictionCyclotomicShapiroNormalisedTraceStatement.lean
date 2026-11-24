module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CorestrictionCyclotomicShapiroNormalisedTrace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.corestriction_cyclotomic_shapiro_normalisedTrace : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ, (∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val) →
  ∀ z : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ → ℚ → Ω, (∀ s x r, z s x r ∈ A) →
  (∀ s t, Stab A s → Stab A t → ∀ x r, CgA A p n (z (s * t) x r) (z s x r + s (z t (x * (χ s)⁻¹) r))) →
  ∀ ξ F : ℚ → Ω, (∀ r, ξ r ∈ A ∧ InZl ε p L (F r)) →
  (∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → χ s = 1 → ∀ tt : ZMod (p ^ n), s (zt ε p (L + n)) = zt ε p n ^ tt.val * zt ε p (L + n) →
    ∀ r, CgA A p n (z s 1 r) (s (ξ r) - ξ r + F r * (tt.val : Ω))) →
  ∀ F' : ℚ → Ω, (∀ r, IsNT ε p L m (F r) (F' r)) →
  ∃ ξ' : ℚ → Ω, (∀ r, ξ' r ∈ A) ∧ ∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → s (zt ε p m) = zt ε p m → ∀ tt : ZMod (p ^ n), IsLamG ε p n m s tt →
    ∀ r, CgA A p n ((p : Ω) ^ c * ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r)
      (s (ξ' r) - ξ' r + (p : Ω) ^ c * (F' r * (tt.val : Ω))) := by
  first | (exact @GlobalTheory.Glue.CorShap.cores_law) | (exact GlobalTheory.Glue.CorShap.cores_law) | (intros; apply GlobalTheory.Glue.CorShap.cores_law  <;> assumption)
