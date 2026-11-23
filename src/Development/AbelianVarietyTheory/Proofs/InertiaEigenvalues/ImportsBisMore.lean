module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.NonzeroScalarLattice

theorem exists_ne_zero_smul_mem {G : Type} [Group G] {LL : Type} [Field LL] {O : Type}
    [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [IsDomain O] [IsFractionRing O LL]
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (w : V) :
    ∃ (b : O), b ≠ (0 : O) ∧ b • w ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T L := by
  have hw : w ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.T.smul_mem _ hax
    · rw [mul_smul]; exact L.T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap O LL q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • ((algebraMap O LL p / algebraMap O LL q) • x) = p • x := by
      rw [← algebraMap_smul LL q, smul_smul, mul_div_cancel₀ _ hq1, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.T.smul_mem _ hax

end GlobalTheory.NonzeroScalarLattice
