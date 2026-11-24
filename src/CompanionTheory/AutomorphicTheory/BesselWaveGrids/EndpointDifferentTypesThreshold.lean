module

public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.AsmDiff
public import CompanionTheory.AutomorphicTheory.CompactTopologicalForms.NormalFormTopDomination
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual

@[expose] public section

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBPEq
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT zuckT_of_zuck zuckDualT_of_zuckDual)

theorem asymptotic_different_types : AsmDiff := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBP.CompactFormNormalFormDomination.thmBpAt_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA _
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA

theorem asymptotic_equal_types : AsmEq := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBPEq.CompactFormNormalFormDomination.thmBpAt_eqR_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf
    hfA _ _
  exact h P Wp Wq p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf hfA

end CompanionTheory.WaveGrid
