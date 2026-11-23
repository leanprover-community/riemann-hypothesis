module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

theorem jDHatOpQQ_of_opA_opR_residue_splitting (hA : JDOpA) (hR : JDOpR) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : JDHatOpQQ := by
  obtain ⟨KA, hKA, hA⟩ := hA
  obtain ⟨KR, hKR, hR⟩ := hR
  refine ⟨max KA KR, le_max_of_le_left hKA, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hGQ hML X hX
  have hAat := hA (max KA KR) (le_max_left _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hML
  have hRat := hR (max KA KR) (le_max_right _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGQ hML
  have hAh : ∀ y, HReal (max KA KR) S T v e L (L.Ahat y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hAat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hAhv : ∀ y, HReal (max KA KR) S T v e L (L.Ahatv y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hAat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hRh : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhM (D.parOf S v) L y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hRat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hRhv : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhvM (D.parOf S v) L y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hRat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hx : ∀ y, xInvM (D.parOf S v) y ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) :=
    fun y => jdh_kap_mem _ L _
  obtain ⟨ν, hνi, hνr⟩ := h4 (D.parOf S v)
  have hR0n : ∀ j, HReal (max KA KR) S T v e L (L.R0 (ν j)) := fun j => by
    rw [h1 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRh _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_SSn_mem _ L l hl))
      (jdh_kap_mem _ L _)) (hAh _)
  have hR0vn : ∀ j, HReal (max KA KR) S T v e L (L.R0v (ν j)) := fun j => by
    rw [h2 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRhv _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_kap_mem _ L _))
      (jdh_SSns_mem _ L l hl)) (hAhv _)
  have key : HReal (max KA KR) S T v e L X := by
    simp only [MA.hatSet, Set.mem_union, Set.mem_range] at hX
    rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
    · exact hAh y
    · rw [(h3 _ L ν hνi y).1]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0n j)
    · exact hAhv y
    · rw [(h3 _ L ν hνi y).2]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0vn j)
  exact key

end

end Formalism.FourierDecayAlt.P.CutMP
