module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectCompleteDVRBothMapsStatement
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem comp_b_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (F : Fam Xo c R)
    {V : Type} [CommRing V] [IsDomain V] (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (h₁ : κ₁ ≫ jK R = jK V ≫ spMap θ₁) (h₂ : κ₂ ≫ jK R = jK V ≫ spMap θ₂) (hy : κ₁ ≫ F.y = κ₂ ≫ F.y) :
    θ₁.comp F.b = θ₂.comp F.b := by
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp F.b) = κ ≫ F.y ≫ pullback.snd _ _ := by
    intro θ κ h
    rw [F.y_over, ← Category.assoc, h, Category.assoc, spMap_comp]
  have e : jK V ≫ spMap (θ₁.comp F.b) = jK V ≫ spMap (θ₂.comp F.b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hy, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this

theorem injBase_cdvr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁.comp (Cn.ψ.comp MvPolynomial.C) = θ₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨o', m₁, m₂, x, h₁, h₂, h₃⟩ :=
    GlobalTheory.T.exists_lowerObject_completeDVR_both_maps Xo c φ hpq hφ hns R hR C Cn V hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hb : (θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = (θ₂.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b := by
    have k : ∀ θ : R →+* V, (θ.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = θ.comp C.b := fun θ => by
      rw [← Cn.base]; rfl
    rw [k, k]
    exact comp_b_eq C.toFam θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  exact Cn.L.fineRed V _ _ hb o' m₁ m₂ x h₁ h₂ h₃

theorem injBase : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁.comp (Cn.ψ.comp MvPolynomial.C) = θ₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn R' _ _ _ hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  haveI : IsNoetherianRing R' := hR'.1.1
  haveI : CharZero R' := hR'.2
  obtain ⟨V, _, _, _, jv, hV, hjv, hjvl⟩ := GlobalTheory.Mum.exists_cDvr_injective_isLocalHom R'
  obtain ⟨κv, hκv⟩ := GlobalTheory.PolDeg.exists_genericMap hjv
  have h := injBase_cdvr Xo c φ hpq hφ hns R hR C Cn V hV (jv.comp θ₁) (jv.comp θ₂) (hjv.comp hθ₁) (hjv.comp hθ₂)
    (RingHom.isLocalHom_comp _ _) (RingHom.isLocalHom_comp _ _) (κv ≫ κ₁) (κv ≫ κ₂)
    (by rw [Category.assoc, hκ₁, ← Category.assoc, hκv, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₂, ← Category.assoc, hκv, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, Category.assoc, hy])
  ext r
  exact hjv (by simpa using DFunLike.congr_fun h r)

end GlobalTheory.UCanon
