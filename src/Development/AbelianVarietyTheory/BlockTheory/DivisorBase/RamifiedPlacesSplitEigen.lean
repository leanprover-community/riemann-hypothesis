module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen

section Frames

variable {S : Scheme.{0}} {R : Type} [CommRing R]

abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)

variable {O : Type} [CommRing O] {G : Over S} [GrpObj G]

def IsEigTan (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsCombAt {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsEigBasis (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigTan act x χ (v i)) ∧ ∀ w, IsEigTan act x χ w → ∃! c : Fin n → R, IsCombAt c v w

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def charIn (c : Coeff l) {R : Type} [CommRing R] (φ : c.F →+* R) (τ : E →+* ℂ) : 𝓞 E →+* R :=
  φ.comp ((τ.codRestrict c.F (c.conj τ)).comp (algebraMap (𝓞 E) E))

def IsFrame (Y : Model Xo c β) (τ : E →+* ℂ) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Y.X)
    (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  x ≫ Y.s = spMap (φ.comp β) ∧ IsEigBasis Y.t.act x (charIn c φ τ) v ∧
    IsEigBasis Y.t.act x (charIn c φ (conjEmb τ)) w

end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
