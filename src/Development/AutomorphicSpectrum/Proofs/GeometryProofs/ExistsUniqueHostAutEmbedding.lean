module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HostAutTrans

theorem existsUnique_hostAut_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [IsGalois ℚ E] (τ τ' : E →+* ℂ), τ (H.rt : E) = H.rt0 → τ' (H.rt : E) = H.rt0 → ∃! g : HostAut H, τ' = τ.comp g.σ.toRingHom := by
  intro E _ _ _ H _ τ τ' hτ hτ'
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ τ'
    (Subsingleton.elim _ _)
  have key : ∀ x, τ' x = τ (σ.symm x) := fun x => by rw [← hσ]; rfl
  refine ⟨⟨σ.symm.toRingEquiv, τ.injective ((key _).symm.trans (hτ'.trans hτ.symm))⟩, ?_, ?_⟩
  · exact RingHom.ext fun x => key x
  · rintro ⟨g₀, hfix⟩ hg
    have hx : ∀ x, g₀ x = σ.symm x := fun x =>
      τ.injective ((RingHom.congr_fun hg x).symm.trans (key x))
    have h0 : g₀ = σ.symm.toRingEquiv := RingEquiv.ext fun x => hx x
    subst h0
    rfl

end GlobalTheory.CompanionTheory.Ar.HostAutTrans
