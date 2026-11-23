module

public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalQuotientHomExt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.GqPt

private theorem hom_ext (q : ℕ) {R : Type} [CommRing R] {f g : LqR q →+* R}
    (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g :=
  _root_.UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext q h

private noncomputable def sec {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

private theorem sec_inj {X : Scheme.{0}} {R : CommRingCat.{0}} {f g : X ⟶ Spec R} (h : sec f = sec g) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)

private theorem sec_to {X : Scheme.{0}} {R : CommRingCat.{0}} (φ : R ⟶ Γ(X, ⊤)) :
    sec (X.toSpecΓ ≫ Spec.map φ) = φ := by
  simp only [sec, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

private theorem val_map_tq (q : ℕ) {T : Scheme.{0}} (s : T ⟶ Gq q) :
    ((Units.map s.appTop.hom.toMonoidHom (tq q) : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) =
      (sec s).hom (LaurentPolynomial.T 1) := rfl

end UpperTheory.GqPt

open UpperTheory.GqPt in
theorem UpperTheory.multiplicativeGroup_hom_existsUnique_of_unit :
    ∀ (q : ℕ) [NeZero q] (T : Scheme.{0}), IsUnit ((q : ℕ) : Γ(T, ⊤)) → ∀ t : (Γ(T, ⊤))ˣ, ∃! s : T ⟶ Gq q, Units.map s.appTop.hom.toMonoidHom (tq q) = t := by
  intro q _ T hq t
  let lam : Localization.Away (q : ℤ) →+* Γ(T, ⊤) :=
    IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom Γ(T, ⊤)) (by simpa using hq)
  let φ : LqR q →+* Γ(T, ⊤) := LaurentPolynomial.eval₂ lam t
  have hφ : φ (LaurentPolynomial.T 1) = t := by
    simp only [φ, LaurentPolynomial.eval₂_T, zpow_one]
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · refine Units.ext ?_
    rw [val_map_tq, sec_to]
    exact hφ
  · intro s hs
    refine sec_inj ?_
    rw [sec_to]
    refine CommRingCat.hom_ext (hom_ext q ?_)
    have h1 := val_map_tq q s
    rw [hs] at h1
    exact h1.symm.trans hφ.symm
