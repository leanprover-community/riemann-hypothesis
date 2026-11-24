module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Formalism.LocalToGlobal.ProjectiveLattices.HeckeStabSet
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

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ThetaTrace

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def IsHeckePrime (l : Level H) (P : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  P.IsMaximal ∧ P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (l.M' : 𝓞 E) ∉ P ∧ p.Prime ∧ (p : 𝓞 E) ∈ P

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def FinAt (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkFin (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)

def TotalAt (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkTotal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
    (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)

def FunAt (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkFun (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
    (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)

def DetectAt (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (ex Dw a n)

end Local

def HeckeFinite : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime l P p → FinAt Xo c P p i

def HeckeTotal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime l P p → TotalAt Xo c P p i

def HeckeSingleValued : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime l P p → FunAt Xo c P p i

def PointsDetect : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DetectAt Xo c a n

def HeckePointLaws : Prop := HeckeFinite ∧ HeckeTotal ∧ HeckeSingleValued ∧ PointsDetect

section Basic₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff {P : Ideal (𝓞 E)} {p : ℕ} :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p ↔ P.IsMaximal ∧ P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      p.Prime ∧ (p : 𝓞 E) ∈ P ∧ ¬ p ∣ l.M' := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime
  constructor
  · rintro ⟨hmax, hsplit, hM, hp, hpP⟩
    refine ⟨hmax, hsplit, hp, hpP, fun hdvd => hM ?_⟩
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul]
    exact P.mul_mem_right _ hpP
  · rintro ⟨hmax, hsplit, hp, hpP, hndvd⟩
    refine ⟨hmax, hsplit, fun hM => hmax.ne_top ?_, hp, hpP⟩
    have hcop : IsCoprime (p : ℤ) (l.M' : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)
    obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom (𝓞 E))
    rw [Ideal.eq_top_iff_one, ← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hM)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection
