module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem isMultiProjPrime_of_vocab (h2 : VocabMultiHomogIdeal.Statement.{u})
    {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {V : Ideal (MRing ι F)}
    (hV : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime V) : IsMultiProjPrime V :=
  ⟨hV.1, (h2 F K ι V).1 hV.2.1, hV.2.2⟩

private theorem finsum_mul_eq_finsupp_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem IntNumIsFieldIntersection.proof (h1 : VocabMultiHomog.Statement.{u})
    (h2 : VocabMultiHomogIdeal.Statement.{u}) (h3 : VocabDivCycle.Statement.{u})
    (h4 : IntNumPoint.Statement.{u}) (h5 : IntNumRatSection.Statement.{u}) :
    IntNumIsFieldIntersection.Statement.{u} := by
  intro F _ K _ _ ι _
  refine ⟨?_, ?_⟩
  · intro V L i hV hi
    have hL : L = (![] : Fin 0 → K → ℤ) := funext fun j => Fin.elim0 j
    subst hL
    exact h4 F K ι V i (isMultiProjPrime_of_vocab h2 hV.1) hV.2 hi
  · intro V n L A f g hV hs
    obtain ⟨α, β, hf, hg, hfV, hgV, hαβ⟩ := hs
    have key := h5 F K ι n V (isMultiProjPrime_of_vocab h2 hV.1) hV.2 L A f g α β
      ((h1 F K ι f α).1 hf) ((h1 F K ι g β).1 hg) hfV hgV hαβ
    refine key.trans ?_
    have hD : ∀ W, ratDiv V f g W = ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g W := by
      intro W
      simp only [ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
      rw [h3 F K ι V f W, h3 F K ι V g W]
    simp only [cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, hD]
    exact finsum_mul_eq_finsupp_sum _ _

end

end GroundTheory.Heights₂.Heights.NumbersDVR
