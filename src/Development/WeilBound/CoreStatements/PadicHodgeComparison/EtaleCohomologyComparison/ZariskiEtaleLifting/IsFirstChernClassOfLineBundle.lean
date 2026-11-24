module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

open CH E

def dlog {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) (v : B) : B :=
  ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : B) * δ.dpow (k + 1) (v - 1)

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((schFn q).cr b ht κ)) (D : LineData X)

def thPt (T : Thick ((schFn q).cr b ht κ)) : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ X := T.y.1.2

def thSp {T T' : Thick ((schFn q).cr b ht κ)} (φ : T ⟶ T') :
    Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ Spec (CommRingCat.of (T.B ⧸ T.J)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle))

structure CLift where
  p : ∀ T : C, Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y
  hp : ∀ T : C, p T ≫ D.f = thPt (G.obj T)
  w : ∀ {T T' : C}, (T ⟶ T') → ((G.obj T').B)ˣ
  hw : ∀ {T T' : C} (φ : T ⟶ T') (h : (thSp (G.map φ) ≫ p T) ≫ D.f = p T' ≫ D.f),
    Ideal.Quotient.mk (G.obj T').J (w φ) =
      (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom (D.u (thSp (G.map φ) ≫ p T) (p T') h)

variable {G D}

def CLift.r (Λ : CLift G D) (s : ComposableArrows C 2) : ((G.obj (s.obj (Fin.last 2))).B)ˣ :=
  Units.map (G.map (s.map' 1 2)).φ.toMonoidHom (Λ.w (s.map' 0 1)) * Λ.w (s.map' 1 2) * (Λ.w (s.map' 0 2))⁻¹

def CLift.coc (Λ : CLift G D) {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ) : Cn (G ⋙ OM _ c) 2 :=
  fun s => (dlog (G.obj (s.obj (Fin.last 2))).δ N (Λ.r s).val : (G.obj (s.obj (Fin.last 2))).B)


variable (D) in
def IsFirstChernClassOfLineBundle {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ) (x : H (OM ((schFn q).cr b ht κ) c) 2) : Prop :=
  ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ Thick ((schFn q).cr b ht κ)) (Λ : CLift G D),
    ∃ hz : d _ 2 (Λ.coc c N) = 0, (cx _).cls _ hz = (Mor.restrict (OM _ c) G).pull 2 x

variable {l : ℕ} [Fact l.Prime]


variable (q D) in
def IsFirstChernFamily (κ : O →+* OC l) (k : Bool) (x : ∀ n, Hc (schFn q) κ k n 2) : Prop :=
  ∀ n, IsFirstChernClassOfLineBundle (q := q) (b := bs l k n) (ht := rfl) (κ := κb κ k n) D ((PAlg.base l).cris n) (l * n) (x n)


variable (l) in
def FirstChernCompatible : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (k : Bool)
  (D : LineData X) (x : ∀ n, Hc (schFn q) κ k n 2), IsFirstChernFamily q D κ k x → E.IsFirstChernClassOfLineBundle q κ D fun n => β (schFn q) κ k n 2 (x n)

end CrystallineSemistableComparison.B
