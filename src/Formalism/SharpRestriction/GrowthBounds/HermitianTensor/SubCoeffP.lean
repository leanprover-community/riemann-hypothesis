module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamAddC
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.RowActTransv
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYGenCoefHom
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
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionEmbedding

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.flipOneThree.Pf.QB

theorem lamMemP : LamMemP := by
  intro K _ _ r N ν ν' νp L hνl hν'l hνpl hνp0 hνpm hPh v hv t ht
  have hsv := fun u => subCoeffP K r ν v hv u
  have hst := fun u => subCoeffP K r ν' t ht u
  obtain ⟨hvw, hvi⟩ := mem_dualWeyl_iff.mp hv
  obtain ⟨htw, hti⟩ := mem_dualWeyl_iff.mp ht
  set F := lamOf K r L (blockEmb K true v * blockEmb K false t) with hF
  have hscale : ∀ t0 : Fin (r + 1 + 1), ∀ c : K, c ≠ 0 →
      scCol K (r + 1 + 1) t0 c F = c ^ νp t0 • F := by
    intro t0 c hc
    rcases midOf_cases t0 with ⟨j, rfl⟩ | ⟨hn, h0 | hl⟩
    · rw [hνpm j]
      exact lam_scaleM L N _ _ hPh j c hc v t hsv hst
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst h0
      rw [hνp0]
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst hl
      rw [hνl, hν'l, hνpl]
  have hcol : ∀ (l j : Fin (r + 1 + 1)), l < j → ∀ c : K, colAdd K l j c F = F := by
    intro l j hlj c
    rcases midOf_cases j with ⟨j', rfl⟩ | ⟨hn, h0 | hl⟩
    · rcases midOf_cases l with ⟨l', rfl⟩ | ⟨hn', h0' | hl'⟩
      · have hne : l' ≠ j' := by
          rintro rfl
          exact lt_irrefl _ hlj
        exact lam_addM L N _ _ hPh l' j' hne c v t hsv hst
      · subst h0'
        exact lam_addC L j' c v t hvi hti
      · subst hl'
        exact absurd hlj (not_lt.mpr (Fin.le_last _))
    · subst h0
      exact absurd hlj (Fin.not_lt_zero _)
    · subst hl
      apply colAdd_trivial
      intro m hm
      rw [wt_of_scale (Fin.last (r + 1)) (νp (Fin.last (r + 1))) F (hscale _) m hm, hνpl]
  rw [mem_dualWeyl_iff]
  refine ⟨?_, ?_⟩
  · intro m hm
    funext t0
    exact wt_of_scale t0 (νp t0) F (hscale t0) m hm
  · intro l j hlj
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (fun φ => φ F) (lsat_eval_colAddGen (R := K) l j x)
    simp only [AlgHom.comp_apply, hcol l j hlj] at h1
    simpa [MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval] using h1

theorem subCoeffP : SubCoeffP := QB.subCoeffP

end Formalism.MainNotions.flipOneThree.Pf

end
