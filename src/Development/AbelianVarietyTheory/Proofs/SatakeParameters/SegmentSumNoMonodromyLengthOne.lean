module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMono0LpCharLpSp
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SegSumOne

theorem segSum_of_mono0 : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))), (segSum rc l).mono0 →
      (∀ Δ ∈ l, Δ.len = 1) ∧ segSum rc l = sumList (l.map fun Δ => rc Δ.first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc l hm
  obtain ⟨a, ha, H⟩ := hrc
  have hlen : ∀ Δ ∈ l, Δ.len = 1 := by
    intro Δ hΔ
    have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
      rw [← H.nu]; exact (H.cusp _ (Δ.isCusp_first.nu _))
    have hmi : (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).mono0 :=
      GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm _ (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)
    have hpos := Δ.len_pos
    by_contra hne
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by omega) hmi
  refine ⟨hlen, ?_⟩
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [hlen Δ hΔ, GlobalTheory.SegLen.lpChar_lpSp_one']
  simp [WD.lpTw_zero]

end GlobalTheory.SegSumOne
