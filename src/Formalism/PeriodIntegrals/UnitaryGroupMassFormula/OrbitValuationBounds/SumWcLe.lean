module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem sum_Wc_le {X : Inst D L} {E : Ent D} (hS : Shape D L X E) {p : ℕ} [Fact p.Prime] (h : OrbOK D p)
    (u : D.what₂.Word) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) :
    ∑ s ∈ (orbLoc E p h u i z Th).TT, ((orbLoc E p h u i z Th).Wc s : ℝ) ≤
      (topsOrb D p z : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
  have hcap : ∀ s, (((orbLoc E p h u i z Th).cap s : ℕ) : ℝ) ≤ L.sc.b + L.etaSz + 1 + 3 * L.Sc := by
    intro s
    have hc := hS.capW u i hi (orbMap D p z s)
    unfold Formalism.MainNotions.OrbitPlaces.Ent.cap at hc
    unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.cap
    by_cases ht : IsTopPl D (orbMap D p z s)
    · have hs : s ∈ (orbLoc E p h u i z Th).TT := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩
      rw [if_pos ht] at hc
      split_ifs
      exact hc
    · have hs : s ∉ (orbLoc E p h u i z Th).TT := fun hs => ht (Finset.mem_filter.1 hs).2
      rw [if_neg ht] at hc
      split_ifs
      exact hc
  have hB0 : 0 ≤ L.sc.b + L.etaSz + 1 + 3 * L.Sc := le_trans (Nat.cast_nonneg _) (hcap 0)
  have hW : ∀ s, (((orbLoc E p h u i z Th).Wc s : ℕ) : ℝ) ≤ L.sc.b + L.etaSz + 1 + 3 * L.Sc := by
    intro s
    have h1 : (orbLoc E p h u i z Th).Wc s ≤ ⌊L.sc.b + L.etaSz + 1 + 3 * L.Sc⌋₊ := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Wc
      apply csSup_le'
      rintro c ⟨j, -, -, rfl⟩
      exact Nat.le_floor (hcap _)
    exact (Nat.cast_le.2 h1).trans (Nat.floor_le hB0)
  calc ∑ s ∈ (orbLoc E p h u i z Th).TT, (((orbLoc E p h u i z Th).Wc s : ℕ) : ℝ)
      ≤ ∑ s ∈ (orbLoc E p h u i z Th).TT, (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := Finset.sum_le_sum (fun s _ => hW s)
    _ = ((orbLoc E p h u i z Th).TT.card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (topsOrb D p z : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
      unfold topsOrb
      rfl

end PI.OrbBoundFW
