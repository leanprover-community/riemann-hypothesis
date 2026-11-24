module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

theorem _root_.GlobalTheory.T.sum_segments_langlands_at_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
        (sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))).lpTw c := by
  intro E Ω _ _ _ _ _ A w
  let _ := GlobalTheory.LocalData.complRel w
  have _ := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc l c
  obtain ⟨a, ha, L⟩ := hrc
  rw [← GlobalTheory.NuShift.sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  have hnu := L.nu Γ.first c
  rw [hnu, WD.lpTw_add, add_comm, ← WD.lpTw_add, GlobalTheory.NuShift.lpChar_lpTw]
  rfl
end
