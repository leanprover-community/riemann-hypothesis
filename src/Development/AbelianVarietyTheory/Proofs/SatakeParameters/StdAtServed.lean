module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

theorem std_at_served : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → 2 * rG L.sc ≤ D.R.k → ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Y.Fl u w hg).t (Y.Fl u w hg).mm (Y.Fl u w hg).c (D.gat u w hg).P.r ((Y.Fl u w hg).TT v) ((Y.Fl u w hg).a v) ((Y.Fl u w hg).b v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) := by
  intro D u w hg L hT X Y hLT hk v
  obtain ⟨hmm, -, -, hr, -⟩ := hLT u w hg
  have hS := (D.gat u w hg).P.setting v
  have hgk := hT.gat_k u w hg
  have hrG : 1 ≤ rG L.sc := Nat.succ_le_succ (Nat.zero_le _)
  have hm2 := D.R.two_le_m
  refine ⟨hg.1, hg.2.1, hS.two_le, hS.even, ?_, ?_, ?_, (Y.Fl u w hg).base v, (D.gat u w hg).P.dom v, ?_, ?_⟩
  · rw [hr]; split_ifs <;> omega
  · rw [hr, hgk]; split_ifs <;> omega
  · rw [hmm]; omega
  · exact fun s => ⟨le_trans (le_max_left _ _) ((Y.Fl u w hg).w_ge v s),
      le_trans (le_max_right _ _) ((Y.Fl u w hg).w_ge v s)⟩
  · exact fun s l hl _ => (Y.Fl u w hg).w_mono v s l hl

end GlobalTheory.TwU
