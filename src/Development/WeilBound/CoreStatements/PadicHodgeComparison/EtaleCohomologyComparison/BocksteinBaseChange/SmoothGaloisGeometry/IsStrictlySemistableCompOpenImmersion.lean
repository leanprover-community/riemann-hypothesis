module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison


theorem isStrictlySemistable_comp_openImmersion {O : Type} [CommRing O] (ϖ : O) {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of O)) (h : GlobalTheory.Et.IsStrictlySemistable ϖ p) (f : Y ⟶ X) [IsOpenImmersion f] :
    GlobalTheory.Et.IsStrictlySemistable ϖ (f ≫ p) := by
  intro y
  obtain ⟨U, hU, hxU, m, r, h1r, hrm, ψ, hψ, hcomp⟩ := h (f.base y)
  obtain ⟨g, hg, hyg⟩ := hU.exists_basicOpen_le (V := f.opensRange) ⟨f.base y, y, rfl⟩ hxU
  haveI := hU.isLocalization_basicOpen g
  haveI : IsIso (f.app (X.basicOpen g)) := f.isIso_app _ hg
  refine ⟨(Opens.map f.base).obj (X.basicOpen g), (hU.basicOpen g).preimage_of_isOpenImmersion f hg, hyg,
    m, r, h1r, hrm,
    (f.app (X.basicOpen g)).hom.comp ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.comp ψ), ?_, ?_⟩
  · have hL : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.Etale :=
      RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway g)
    have h2 := RingHom.Etale.stableUnderComposition _ _ hψ hL
    exact (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom _) (f.app (X.basicOpen g))).mpr h2
  · rw [RingHom.comp_assoc, RingHom.comp_assoc, hcomp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    have key : ∀ e₁ e₂, p.appLE ⊤ U e₁ ≫ X.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫
        f.app (X.basicOpen g) = (f ≫ p).appLE ⊤ ((Opens.map f.base).obj (X.basicOpen g)) e₂ := by
      intro e₁ e₂
      rw [← Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ t) (key _ _)

end CrystallineSemistableComparison
