module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SrcHalf
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem ycond_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ}
    (h : M' ≤ M) : YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j M := by
  unfold YCond
  apply sSup_le_sSup
  rintro S ⟨hS1, hS2⟩
  refine ⟨le_trans hS1 ?_, hS2⟩
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

theorem yjt_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ)
    {M M' : Fin q → WithTop ℤ} (h : ∀ k, M' k ≤ M k) : Yjt K (r := r) LL J M' ≤ Yjt K (r := r) LL J M :=
  inf_le_inf_left _ (iInf_mono fun k => ycond_mono' (K := K) (r := r) LL (J k) (h k))

theorem map_floor_mono (x : WithTop ℤ) {m m' : ℝ} (h : m ≤ m') :
    x.map (fun y : ℤ => ⌊(y : ℝ) - m'⌋) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - m⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact Int.floor_mono (by linarith)

theorem monoAt : MonoAt := by
  intro O _ _ p r _ s S aTop aPlus b m m' hmm
  unfold BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ (fun k => map_floor_mono _ hmm) hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

end Formalism.MainNotions.ColumnSystems.Pf
