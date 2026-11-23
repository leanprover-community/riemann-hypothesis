module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mem_V_of_forall (W : ValuationSubring ℂ) (h : ∀ p : ℕ, p.Prime → (p : ℂ) ∉ W.nonunits) (x : c.F) :
    x ∈ c.V W := by
  have hv1 : ∀ n : ℕ, n ≠ 0 → W.valuation (n : ℂ) = 1 := by
    intro n hn
    induction n using Nat.recOnMul with
    | zero => exact absurd rfl hn
    | one => simp
    | prime p hp =>
      refine le_antisymm ((W.valuation_le_one_iff _).2 (natCast_mem W p)) (not_lt.1 fun hlt => h p hp ?_)
      exact (W.mem_nonunits_iff).2 hlt
    | mul a b iha ihb =>
      have ha : a ≠ 0 := left_ne_zero_of_mul hn
      have hb : b ≠ 0 := right_ne_zero_of_mul hn
      rw [Nat.cast_mul, map_mul, iha ha, ihb hb, one_mul]
  have hvi : ∀ n : ℤ, n ≠ 0 → ((n : ℂ))⁻¹ ∈ W := by
    intro n hn
    have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    have e : W.valuation (n : ℂ) = 1 := by
      rcases Int.natAbs_eq n with h1 | h1
      · rw [h1, Int.cast_natCast]; exact hv1 _ hn'
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact hv1 _ hn'
    refine (W.valuation_le_one_iff _).1 ?_
    rw [map_inv₀, e, inv_one]
  haveI := c.fin
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := x)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))
  let i : c.F →+* ℂ := c.F.val.toRingHom
  have h1 : _root_.IsIntegral ℤ (i (n • x)) := hint.map i.toIntAlgHom
  have h2 : _root_.IsIntegral W (i (n • x)) := h1.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : i (n • x) ∈ W := by
    have hw' : (w : ℂ) = i (n • x) := hw
    rw [← hw']; exact w.2
  have h4 : i x = ((n : ℂ))⁻¹ * i (n • x) := by
    have hn0 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [zsmul_eq_mul, map_mul, map_intCast, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  change i x ∈ W
  rw [h4]
  exact W.mul_mem _ _ (hvi n hn) h3

theorem isOpenImmersion_j (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ (p : ℂ) ∈ W.nonunits
  · obtain ⟨p, hp, hW⟩ := h
    exact GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  · push_neg at h
    have hbij : Function.Bijective (c.V W).subtype :=
      ⟨Subtype.val_injective, fun x => ⟨⟨x, mem_V_of_forall W h x⟩, rfl⟩⟩
    have h1 : IsIso (CommRingCat.ofHom (c.V W).subtype) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso (spMap (c.V W).subtype) := by
      unfold spMap; infer_instance
    have := Y.jQ_open
    unfold Model.j
    infer_instance

end GlobalTheory.TriplesAlong

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.TriplesAlong

