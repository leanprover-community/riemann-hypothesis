module

public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleFinrankOne.IrrOfFinrankOne
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory

theorem absIrrChar_comp_mem_gxIrrSet : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K]
    [inst_3 : CharZero K] (σ : K →+* ℂ) (χ : G → K), IsAbsIrrChar χ →
    (fun g => σ (χ g)) ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ := by
  intro G _ _ K _ _ σ χ h
  classical
  obtain ⟨⟨n, ρc, htr⟩, hip⟩ := PI.XgCTieBrWork.Chars.absIrr_isIrr σ h
  have htr' : ∀ x, σ (χ x) = Matrix.trace ((ρc x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := htr
  have hchar : ∀ x, (PI.XgCTieBrWork.Chars.ofGL ρc).character x = σ (χ x) := fun x => by
    rw [PI.XgCTieBrWork.Chars.char_ofGL, htr']
  haveI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have hfr := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (PI.XgCTieBrWork.Chars.ofGL ρc) (PI.XgCTieBrWork.Chars.ofGL ρc)
  have hsum : ∑ g : G, (PI.XgCTieBrWork.Chars.ofGL ρc).character g *
      (PI.XgCTieBrWork.Chars.ofGL ρc).character g⁻¹ = (Nat.card G : ℂ) := by
    simp_rw [hchar]
    rw [Nat.card_eq_fintype_card, ← hip]
    unfold Formalism.L2.NT.ipG
    refine Finset.sum_congr rfl fun x _ => ?_
    show σ (χ x) * σ (χ x⁻¹) = σ (χ x) * star (σ (χ x))
    rw [htr' x, htr' x⁻¹, PI.XgCTieBrWork.Chars.star_trace_inv]
  rw [hsum, inv_mul_cancel₀ (NeZero.ne _)] at hfr
  have h1 : Module.finrank ℂ (Representation.IntertwiningMap (PI.XgCTieBrWork.Chars.ofGL ρc)
      (PI.XgCTieBrWork.Chars.ofGL ρc)) = 1 := by
    exact_mod_cast hfr.symm
  exact ⟨n, PI.XgCTieBrWork.Chars.ofGL ρc, PI.XgCTieBrWork.Chars.irr_of_finrank_one _ h1, funext hchar⟩

end GlobalTheory
