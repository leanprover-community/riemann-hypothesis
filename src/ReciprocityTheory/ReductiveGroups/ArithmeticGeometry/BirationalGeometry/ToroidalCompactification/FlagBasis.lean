module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

set_option linter.dupNamespace false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField IsLocalRing MvPolynomial
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Tan

variable {V : Type} [CommRing V]

abbrev ptOver (V R : Type) [CommRing V] [CommRing R] [Algebra V R] : Over (Sp V) :=
  Over.mk (spMap (algebraMap V R))

abbrev epsOver (V R : Type) [CommRing V] [CommRing R] [Algebra V R] : Over (Sp V) :=
  Over.mk (spMap ((algebraMap R (DualNumber R)).comp (algebraMap V R)))

def epsMul {R : Type} [CommRing R] (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

variable {R : Type} [CommRing R] [Algebra V R] {G : Over (Sp V)} [GrpObj G]

def IsTan (v : epsOver V R ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : ptOver V R ⟶ G).left

def IsComb {m : ℕ} (v : Fin m → (epsOver V R ⟶ G)) (c : Fin m → R) (w : epsOver V R ⟶ G) : Prop :=
  ∃ u : Fin m → (epsOver V R ⟶ G), (∀ i, (u i).left = spMap (epsMul (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

end Tan

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure ValPt (Y : Model Xo c β) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  K' : Type
  [fld : Field K']
  [alg : Algebra V K']
  [frac : IsFractionRing V K']
  complete : IsAdicComplete (maximalIdeal V) V
  char0 : CharZero K'
  oV : O →+* V
  fK : c.F →+* K'
  compat : (algebraMap V K').comp oV = fK.comp β
  y : Sp K' ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = spMap fK
  yt : Sp V ⟶ Y.X
  yt_over : yt ≫ Y.s = spMap oV
  ext : spMap (algebraMap V K') ≫ yt = y ≫ Y.j
  G : SAB H (Sp V)
  pull : SABMap G Y.t yt

attribute [instance] ValPt.ring ValPt.dom ValPt.dvr ValPt.fld ValPt.alg ValPt.frac

variable {Y : Model Xo c β}

def Datum.mult (D : Datum H) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then D.p else D.q

def conjEmb (τ : E →+* ℂ) : E →+* ℂ := (starRingEnd ℂ).comp τ

section Letters

variable (D) (n : ℕ)

variable {D n}

end Letters

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
