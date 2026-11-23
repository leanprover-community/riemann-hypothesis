module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSupBound
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
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
import Mathlib.RingTheory.SimpleRing.Principal
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnGenericDeg_of_semipos (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) {P P0 : Ideal (MRing ι)} {M : HermLine ι}
    (hP0 : P0 ≤ P) (hs : IsSemipositiveRel P0 P M) : NefOnGenericDeg P M.a := by
  classical
  intro W hW hPW
  have h1 : 0 ≤ geomDeg W M 1 := hN K ι P P0 M hP0 hs W hW hPW
  have h2 := hD K ι W 1 (fun _ => M) hW (fun _ => hs.1)
  have h3 : geomDeg W M 1 = (genDeg W 1 M.a : ℝ) := by
    rw [geomDeg, genDeg]
    convert h2 using 2
    rfl
  exact_mod_cast h3 ▸ h1

theorem continuousOn_zcomb_fsH {M : HermLine ι} (hM : IsSmoothHerm M) (k : ℤ) :
    ContinuousOn (HermLine.zcomb M (fsH ι) k (-1)).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hH : ContinuousOn (fsH ι).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).continuousOn
  exact (hM.continuousOn.zpow₀ k fun z hz => Or.inl (M.pos z hz).ne').mul
    (hH.zpow₀ (-1) fun z hz => Or.inl ((fsH ι).pos z hz).ne')

theorem KodairaSection.proof (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) (hK : KodairaGeneric.Statement)
    (hC : ChartDenominator.Statement) (hS : SectionSupBound.Statement) : KodairaSection.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 hD1 har hb hM
  obtain ⟨k, e, hk, he0, heQ⟩ :=
    hK K ι Ω y D M.a hD1 har hb (nefOnGenericDeg_of_semipos hN hD hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos) hM.big
  obtain ⟨n, hn, hne⟩ := hC K ι Ω y _ 1 e heQ
  have ha : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
    ring
  obtain ⟨C, hC0, hB⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) k (-1)) 1 ((n : Ω) * e)
    (continuousOn_zcomb_fsH hM.semipos.1 k) (by rw [ha]; exact hne)
  exact ⟨k, (n : Ω) * e, C, hk, hC0, mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he0, hne, hB⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
