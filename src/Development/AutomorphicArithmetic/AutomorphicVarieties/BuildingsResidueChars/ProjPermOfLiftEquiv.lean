module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.projPerm_of_liftEquiv :
    UpperTheory.V.Af.BA.LiftEquiv → UpperTheory.V.Af.BA.ProjPerm := by
  intro h Γ X _ _ hfin
  refine CategoryTheory.Projective.mk ?_
  intro E Y f e he
  have hs := (Rep.epi_iff_surjective e).1 he
  have heq : ∀ (g : Γ) (x : X), (Rep.Hom.hom f) (Finsupp.single (g • x) 1) =
      (Y.ρ g) ((Rep.Hom.hom f) (Finsupp.single x 1)) := by
    intro g x
    have hc := LinearMap.congr_fun ((Rep.Hom.hom f).isIntertwining' g) (Finsupp.single x 1)
    simpa [UpperTheory.V.Af.BA.permC_single] using hc
  obtain ⟨ψ, hψ, hψe⟩ := h Γ X hfin E Y e hs (fun x => (Rep.Hom.hom f) (Finsupp.single x 1)) heq
  refine ⟨Rep.ofHom (ρ := UpperTheory.V.Af.BA.permC Γ X) (σ := E.ρ)
    ⟨Finsupp.linearCombination ℂ ψ, ?_⟩, ?_⟩
  · intro g
    apply Finsupp.lhom_ext
    intro x c
    simp [UpperTheory.V.Af.BA.permC_single, hψ]
  · apply UpperTheory.V.Af.BA.PC_ext
    intro x
    simp [Rep.hom_comp, Rep.hom_ofHom, hψe]
