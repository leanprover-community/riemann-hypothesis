module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
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

@[expose] public section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem colon_map_expand_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤
      colon (O := O) (K := K) (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => hα (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by

      rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring

end GlobalTheory.LiftCoker
