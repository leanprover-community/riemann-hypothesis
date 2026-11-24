module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
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

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem SzRow.and {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P) (hQ : SzRow Q) :
    SzRow (fun C D L => P C D L ∧ Q C D L) := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  obtain ⟨b1, hb1⟩ := hQ eps h0 h1 C hC
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  refine ⟨max a3 b3, fun D L he hx hV => ⟨?_, ?_⟩⟩
  · exact ha3 D L he (le_trans (le_max_left _ _) hx) hV
  · exact hb3 D L he (le_trans (le_max_right _ _) hx) hV

theorem SzRow.imp {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P)
    (h : ∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) : SzRow Q := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun D L he hx hV => h C cD ch D L hC hV (ha3 D L he hx hV)⟩

theorem szRow_and_imp :
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P → SzRow Q → SzRow (fun C D L => P C D L ∧ Q C D L)) ∧
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P →
      (∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) → SzRow Q) :=
  ⟨fun _ _ hP hQ => hP.and hQ, fun _ _ hP h => hP.imp h⟩

end GlobalTheory.EX
