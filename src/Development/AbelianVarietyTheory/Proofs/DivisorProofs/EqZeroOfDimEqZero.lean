module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem isIso_hom_of_dim_eq_zero {K : Type} [Field K] (A : AbVar K) (h : A.dim = 0) : IsIso A.X.hom := by
  have hA := A.ab
  have : IsProper A.X.hom := hA.proper
  have hs : SmoothOfRelativeDimension 0 A.X.hom := h ▸ A.smooth
  have : Etale A.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  let e : Sp K ⟶ A.X.left := (1 : 𝟙_ (Over (Sp K)) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over (Sp K)) ⟶ A.X)
  have : IsOpenImmersion e := isOpenImmersion_of_section_of_etale A.X.hom e he
  have : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ A.X.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.X.hom
  obtain ⟨hI, -, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  have : ConnectedSpace A.X.left := inferInstance
  have hne : (Set.range e).Nonempty := ⟨_, (default : PrimeSpectrum K), rfl⟩
  have hsurj : Function.Surjective e := Set.range_eq_univ.1
    (IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩ hne)
  have : Surjective e := ⟨hsurj⟩
  have : IsIso e := IsOpenImmersion.isIso e
  have : IsIso (e ≫ A.X.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e A.X.hom

theorem hom_eq_of_isIso {K : Type} [Field K] {A : AbVar K} (h : IsIso A.X.hom) {T : Over (Sp K)}
    (g₁ g₂ : T ⟶ A.X) : g₁ = g₂ := by
  ext
  rw [← cancel_mono A.X.hom, Over.w, Over.w]

theorem eq_zero_of_dim_eq_zero :
    ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  intro K _ A B h f
  rcases h with h | h
  · have hi := isIso_hom_of_dim_eq_zero A h
    apply Subtype.ext
    change f.hom = (0 : A ⟶ B).hom
    rw [zero_hom]
    have e1 : f.hom = (1 : A.X ⟶ A.X) ≫ f.hom := by
      rw [hom_eq_of_isIso hi (1 : A.X ⟶ A.X) (𝟙 A.X), Category.id_comp]
    rw [e1, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  · have hi := isIso_hom_of_dim_eq_zero B h
    apply Subtype.ext
    exact hom_eq_of_isIso hi _ _

end GlobalTheory.AV.AbVar
