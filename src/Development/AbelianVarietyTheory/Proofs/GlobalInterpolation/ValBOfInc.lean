module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem valB_of_inc : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT) (v : X.A.vT) (p p₁ : M.Pt), X.fm.seenP w = true → v ∈ V → M.Inc v p p₁ → Co.valB w V p₁ = Co.valB w (V.erase v) p := by
  intro D u X i M Co w V v p p₁ hw hv hI
  obtain ⟨-, hoff, x, -, -, hk, -⟩ := hI
  have key : ∀ v', (if X.fm.seenP w = true ∧ v' ∉ V then ((p₁.2 v').1.L : Set _) else (p₁.2 v').ker) =
      (if X.fm.seenP w = true ∧ v' ∉ V.erase v then ((p.2 v').1.L : Set _) else (p.2 v').ker) := by
    intro v'
    by_cases h : v' = v
    · subst h
      rw [if_neg (fun h => h.2 hv), if_pos ⟨hw, Finset.notMem_erase _ _⟩, hk]
    · rw [hoff v' h]
      have : v' ∈ V.erase v ↔ v' ∈ V := by simp [h]
      simp only [this]
  unfold PtModel.Coord.valB
  simp only [key]

end GlobalTheory.LvT
