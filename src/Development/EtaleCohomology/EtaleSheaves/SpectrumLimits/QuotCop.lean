module

public import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
import Development.EtaleCohomology.EtaleSheaves.CechLevels
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

theorem quotCop : QuotCop := by
  intro A A' B _ _ _ φ χ ι l hl I hcop R _ g c hg
  have hg' : ∀ i, ((g i).comp (Ideal.Quotient.mk (I.map φ))).comp φ = c.comp (Ideal.Quotient.mk I) := by
    intro i
    rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, hg i]
  obtain ⟨h', ⟨h'l, h'c⟩, h'u⟩ := hcop R _ _ hg'
  have hk : ∀ b ∈ I.map χ, h' b = 0 := by
    intro b hb
    have : I.map χ ≤ RingHom.ker h' := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change h' (χ a) = 0
      rw [← RingHom.comp_apply, h'c, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact this hb
  refine ⟨Ideal.Quotient.lift _ h' hk, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, lq, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' (l i), h'l i, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, qm, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' χ, h'c, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    have : h2.comp (Ideal.Quotient.mk _) = h' := by
      apply h'u
      refine ⟨fun i => ?_, ?_⟩
      · rw [RingHom.comp_assoc, ← Ideal.quotientMap_comp_mk (le_l φ χ (l i) (hl i) I), ← RingHom.comp_assoc]
        exact congrArg (fun f => RingHom.comp f (Ideal.Quotient.mk (I.map φ))) (h2l i)
      · rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, h2c]
    rw [this]
    ext x
    simp

end LateralTheory.E.LevelsGenPf
