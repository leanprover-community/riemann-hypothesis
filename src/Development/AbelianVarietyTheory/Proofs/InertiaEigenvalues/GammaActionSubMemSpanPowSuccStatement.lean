module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionSubMemSpanPowSucc
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem _root_.GlobalTheory.T.gammaAction_sub_mem_span_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  intro D HW l _ K s LL h W g hg
  have hχ := (W.GKs_def g).1 hg
  rw [← W.χΓ_res g] at hχ
  have hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ) := by exact_mod_cast W.s_pos
  obtain ⟨c, hc⟩ := GlobalTheory.GamFilt.exists_eq_one_add (D.loc l) LL _ (hs.trans hχ)
  exact GlobalTheory.GamFilt.letγ_sub_mem (W.γ₀ (W.resΓ g)) l c
    (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)
