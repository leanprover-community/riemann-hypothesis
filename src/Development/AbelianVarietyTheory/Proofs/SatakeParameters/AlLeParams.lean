module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.DataKerI
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRowsParams
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
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
import Mathlib.Tactic.Linter.Style
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

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.AlTop

theorem al_le_rowLen_sub {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (t : HH D) (ht : t ∈ D.host.TT) :
    al L (aL L) t ≤ (((nuD D u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD D u j (false, t)).rowLen 1 : ℕ) : ℝ) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega
  have hz : IsTopPl D (false, t) := ⟨rfl, ht⟩
  obtain ⟨e1, -⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl L u j hj (false, t) hz
  have hwe : wPl D (j + 1) (false, t) = (((D.hcW u (tauPl D (false, t))).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  obtain ⟨-, h4⟩ := L.cloud_u u (tauPl D (false, t)) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < D.R.k; omega)
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hS := L.Sc_pos
  rw [nuRowOK D u j hj, nuRowOK D u j hj, ite_eq_left (by omega), ite_eq_left (by omega), e1,
    RowWeightLemmas.nuRow_head D u j hj _ 1 (by omega), hwe]
  unfold al cG kaJ Ranks.N
  push_cast
  linarith

theorem al_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, al (Fm.L x i) (aL (Fm.L x i)) t ≤ (((nuD (Fm.D x i) u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD (Fm.D x i) u j (false, t)).rowLen 1 : ℕ) : ℝ) :=
  fun Fm => ⟨0, fun x _ _ i u j hj t ht => al_le_rowLen_sub (Fm.L x i) u j hj t ht⟩

end GlobalTheory.AlTop
