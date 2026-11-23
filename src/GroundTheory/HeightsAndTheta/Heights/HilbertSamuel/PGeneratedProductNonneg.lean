module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedRestrict
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedEffectiveSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedProductNonneg

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_ratDiv {V : Ideal (MRingOver F ι)} {f g : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (hW : W ∈ (ratDiv V f g).support) : V ≤ W := by
  have key : ∀ s : MRingOver F ι, ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → V ≤ W := by
    intro s hs
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hs
    rw [Finsupp.ofSupportFinite_coe] at hs
    split_ifs at hs with h
    · exact le_sup_left.trans h.1.1.2
    · exact absurd rfl hs
  rw [Finsupp.mem_support_iff, ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g fun h => hW ?_
    rw [hf, h]
    simp
  · exact key f hf

end GeneratedProductNonneg

theorem GeneratedProductNonneg.proof (hR : GeneratedRestrict.Statement)
    (hE : GeneratedEffectiveSection.Statement) : GeneratedProductNonneg.Statement := by
  classical
  intro F _ K _ _ ι _ _ I V m β hI hV hgen
  induction m generalizing V with
  | zero =>
    choose i hi using hV.1.2.2
    rw [hI.1 V β i hV hi]
    exact Int.natCast_nonneg _
  | succ m ih =>
    obtain ⟨f, g, hs, heff⟩ := hE F K ι V (β (Fin.last m)) hV.1 (hgen (Fin.last m))
    have e := hI.2 V m (Fin.init β) (β (Fin.last m)) f g hV hs
    rw [Fin.snoc_init_self] at e
    rw [e, cycEval]
    refine Finsupp.sum_nonneg fun W hW => mul_nonneg (heff W) ?_
    obtain ⟨α, γ, hf, hg, hfV, hgV, -⟩ := hs
    have hWm : IsProjVarF W m := KleimanNefF.isProjVarF_of_mem_support hV
      ((NumbersDVR.VocabMultiHomog.proof F K ι f α).1 hf) ((NumbersDVR.VocabMultiHomog.proof F K ι g γ).1 hg)
      hfV hgV hW
    have hle : V ≤ W := GeneratedProductNonneg.le_of_mem_support_ratDiv hW
    exact ih W (Fin.init β) hWm fun j => hR F K ι V W _ hle (hgen _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
