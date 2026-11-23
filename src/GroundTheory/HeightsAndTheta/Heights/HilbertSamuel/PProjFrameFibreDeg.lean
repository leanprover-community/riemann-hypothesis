module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibreDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatioFieldDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtRel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtTransc
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameFibreDeg.proof (hPt : ProjFrameFibrePt.Statement) (hRel : ProjFrameGenPtRel.Statement)
    (hTr : ProjFrameGenPtTransc.Statement) (hDeg : TranscRatioDeg.Statement) (hRat : RatioFieldDeg.Statement) :
    ProjFrameFibreDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF G i hi
  obtain ⟨hc, hcoord, hrel, hrange⟩ := hRel D Ω κ x e hP hF G
  have : CharZero G.Φ' := charZero_of_inj_zero hc

  have hz : ∀ k, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]; exact h)
  have hch := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz
    (hPt D Ω κ x e hP hF G).1.2.1
  let k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) := ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩
  let u : Ix κ → G.Φ' := fun p => G.x' ⟨Sum.inl p.1, p.2⟩
  have hset : (Set.range fun q : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) = Set.range fun p : Ix κ => u p / u ⟨(), i k₀⟩ := by
    ext c
    constructor
    · rintro ⟨⟨⟨(t | t), h⟩, j⟩, rfl⟩
      · exact ⟨⟨(), j⟩, rfl⟩
      · exact absurd ⟨t, rfl⟩ h
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨⟨k₀, j⟩, rfl⟩
  change ptDeg (RingHom.ker _) i = _
  rw [hch, hset]
  rw [hDeg (Ix κ) G.Φ' u D e (fun k => G.x' ⟨Sum.inr (), k⟩) ⟨(), i k₀⟩ G.Φ (hz k₀)
    (fun k => ProjFrameGraph.genFibre_x'_ne_zero G (e k).2 (ProjFrameGraph.frame_ne_zero hF k)) hrel
    (hTr D Ω κ x e hP hF G) hrange]
  exact hRat (Ix κ) G.Φ' Ω u x D e hcoord

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
