module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftSm :
    UpperTheory.V.Af.Nf.LiftSm := by
  intro k M hM f φ hφ
  refine ⟨fun γ g => ?_, fun u hu g => ?_, fun hf g => ?_⟩
  · obtain ⟨γ', h, u, hu, rfl⟩ := decomp M hM g
    rw [← mul_assoc, ← map_mul, hφ _ _ _ hu, hφ _ _ _ hu]
  · obtain ⟨γ', h, u', hu', rfl⟩ := decomp M hM g
    rw [mul_assoc, mul_assoc, ← map_mul, hφ _ _ _ hu', hφ _ _ _ (mul_mem hu' hu)]
  · obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
    let L : TR.Lie ℚ 2 → (Fin 2 → Fin 2 → ℝ) := fun x i j => ∑ l, h.val i l * x l j Rat.infinitePlace
    have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L := by
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ContDiff.sum fun l _ => contDiff_const.mul ?_
      exact (contDiff_apply ℝ _ Rat.infinitePlace).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ l))
    have hLy : ∀ y : GL (Fin 2) (TR.Rinf ℚ),
        Matrix.of (L (TR.toL y.val)) = (h * Matrix.GeneralLinearGroup.map ev y).val := fun y => rfl
    refine ((archSm k f hf).comp hL.contDiffOn fun x hx => ?_).congr fun x hx => ?_
    · obtain ⟨y, hy⟩ := id hx
      have e : x = TR.toL y.val := hy.symm
      subst e
      change (Matrix.of (L (TR.toL y.val))).det ≠ 0
      rw [hLy]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
    · obtain ⟨y, hy⟩ := id hx
      have e : x = TR.toL y.val := hy.symm
      subst e
      rw [TR.chart_val, ← upR_ev, mul_assoc, mul_assoc, ← upR_comm, ← mul_assoc (upR h), ← map_mul, hφ _ _ _ hu,
        Function.comp_apply, arch, hLy]
