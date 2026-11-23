module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem inputs_of_subset_widths : ∀ S S' : Set ℝ, S ⊆ S' → (AmpOn S' → AmpOn S) ∧ (SmallOn S' → SmallOn S) ∧ (CntOn S' → CntOn S) ∧ (CountBoundOn S' → CountBoundOn S) ∧ (TieOn S' → TieOn S) := by
  intro S S' hSS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h Cg cb Cu cT CT hb hT
    obtain ⟨C, C2, Ch, h1, h2, h3⟩ := h Cg cb Cu cT CT hb hT
    refine ⟨C, C2, Ch, h1, h2, fun Cpr δ hδ => ?_⟩
    obtain ⟨thr, ht⟩ := h3 Cpr δ hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT δ hb hT hδ
    obtain ⟨thr, ht⟩ := h Cg cb Cu cT CT δ hb hT hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, cS, c4, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, cS, c4, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨cV, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨cV, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩

end GlobalTheory.Core.Deg
