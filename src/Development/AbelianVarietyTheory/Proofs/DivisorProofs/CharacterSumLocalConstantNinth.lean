module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.Columns.BaseLemmas
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ColNorms.StepRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem nuW_eq_nu (N : NumDatum) {X : Fields} {Pr : Primes X} (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word)
    (δ : Code N) (h : WeightTie N W pl u δ) {i : ℕ} (hi : i < N.R.m) (z : RPl N.R) (l : Fin (N.R.N i)) :
    (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  obtain ⟨h1, h2⟩ := h.2.2 z
  have he : (W.hc u (pl z)).e = (N.hc z).e := congrArg RowPar.e h1
  have hq : N.eQ (i + 1) z = (N.hc z).e ⟨i, hi⟩ := by
    unfold NumDatum.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [W.nuW_eq u hi, W.lamN_eq u hi.le, he]
  unfold NumDatum.nu NumDatum.srcPar
  rw [hq]
  by_cases hl : l.1 < N.R.k
  · rw [dite_eq_left hl, dite_eq_left hl]
    unfold hcToWeightQ rhoVec wG Ranks.N
    rw [h2, Nat.add_sub_cancel]
    push_cast
    ring
  · have hb := N.R.blk_lt hi.le l hl
    rw [dite_eq_right hl, dite_eq_right hl, dite_eq_left hb]
    have hdm := Nat.div_add_mod (l.1 - N.R.k) (N.R.t + 1)
    have hl2 : l.1 = N.R.k + ((N.R.t + 1) * ((l.1 - N.R.k) / (N.R.t + 1)) + (l.1 - N.R.k) % (N.R.t + 1)) := by omega
    have hl3 : ((l.1 : ℕ) : ℚ) = N.R.k + (((N.R.t : ℚ) + 1) * (((l.1 - N.R.k) / (N.R.t + 1) : ℕ) : ℚ) +
        (((l.1 - N.R.k) % (N.R.t + 1) : ℕ) : ℚ)) := by exact_mod_cast hl2
    rw [hl3]
    generalize (N.hc z).e ⟨(l.1 - N.R.k) / (N.R.t + 1), hb⟩ = eb
    generalize (l.1 - N.R.k) / (N.R.t + 1) = B
    generalize (l.1 - N.R.k) % (N.R.t + 1) = r
    unfold wG Ranks.N
    rw [Nat.add_sub_cancel]
    push_cast
    ring

theorem sExp_int (R : Ranks) (z : ℤ) (j : ℕ) :
    (∃ y : ℤ, sExp R (z : ℚ) (j + 1) = y) ∧ ∃ y : ℤ, sExp' R (z : ℚ) (j + 1) = y := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold sExp sExp' Ranks.N
  rw [Nat.add_sub_cancel, ha, hc]
  exact ⟨⟨z - a - j * (c + 1), by push_cast; ring⟩, ⟨z - a - (j + 1) * (c + 1), by push_cast; ring⟩⟩

theorem stepWeights {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau)
    (h0 : ∀ l : Fin (R.N i), 0 ≤ (W.nuW u (i + 1) τ).w l) :
    GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ) := by
  obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨i, hi⟩
  obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩ := sExp_int R z i
  refine ⟨h0, ⟨y', fun l => ?_⟩, ⟨y, fun l => ?_⟩⟩
  · have h := W.nuW_eq_true u hi τ l
    rw [hz, hy'] at h
    exact_mod_cast h
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero
    by_cases hl : l.1 < R.N i
    · rw [dite_eq_left hl]
      have h := W.nuW_eq_true u hi τ ⟨l.1, hl⟩
      have h' := W.lamTrue_old u hi τ l hl
      rw [hz, hy'] at h
      rw [hz, hy, hy', ← h] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = (((W.nuW u (i + 1) τ).w ⟨l.1, hl⟩ : ℤ) : ℚ) := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2
    · rw [dite_eq_right hl]
      have h' := W.lamTrue_new u hi τ l hl
      rw [hz, hy] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = 0 := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2

end GlobalTheory.ColNorms.StepRows
