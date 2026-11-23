module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocalStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
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

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_card_le_card_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE
  classical
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tFin F δ S
      = ∑ v ∈ S, if ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) then 1 else 0 := by
    rw [← Finset.card_filter, tFin, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨w, w', hne, hw, hw'⟩ := GlobalTheory.T.exists_two_places_over_of_isSquare_local F E δ θ σ hq v hs
    have : 1 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.one_lt_card.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩,
        w', Finset.mem_filter.2 ⟨(hSE w').2 (hw' ▸ hv), hw'⟩, hne⟩
    omega
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega

end GlobalTheory.QNorm
