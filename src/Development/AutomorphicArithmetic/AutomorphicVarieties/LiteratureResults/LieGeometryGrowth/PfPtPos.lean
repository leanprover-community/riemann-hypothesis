module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Geo.Pf.ptPos :
    UpperTheory.V.Lit.Geo.Pf.PtPos := by
  intro E _ _ _ a Ξ χ G hG n e he q α
  have hnn : ∀ v : Fin Ξ.d → ℂ, 0 ≤ star v ⬝ᵥ G *ᵥ v := fun v => hG.pos.posSemidef.dotProduct_mulVec_nonneg v
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have h : 0 ≤ ptIp χ G e α α g :=
      mul_nonneg (Complex.zero_le_real.2 (by positivity)) (Finset.sum_nonneg fun I _ => hnn _)
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
    exact ⟨_, h1, Complex.ext rfl h2.symm⟩
  · have h2 : ∀ I : Fin q → Fin n, (α fun i => e (I i)) = 0 := fun I => by
      have hev : ∀ g, ev (α fun i => e (I i)) g = 0 := fun g => by
        have h := h0 g
        rw [ptIp, mul_eq_zero] at h
        rcases h with h | h
        · simp at h
        · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hnn _)).1 h I (Finset.mem_univ _)
          by_contra hne
          exact (hG.pos.dotProduct_mulVec_pos hne).ne' h1
      rw [← sum_cmp (α fun i => e (I i))]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : cmp j (α fun i => e (I i)) = 0 := Subtype.ext (funext fun g => by
        rw [Pf.cmp_ev, hev]; rfl)
      rw [this, TensorProduct.zero_tmul]
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : α X = ∑ I : Fin q → Fin n, α fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact α.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [α.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
