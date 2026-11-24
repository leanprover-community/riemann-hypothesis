module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pairings

variable {S : Scheme.{0}} {A B G G' : Over S} [GrpObj A] [GrpObj B] [GrpObj G] [GrpObj G']

def WeilEqAt (k : ℕ) (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') :
    Prop :=
  ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B), x ^ k = 1 → y ^ k = 1 → ∀ c : Γ(T.left, ⊤)ˣ,
    Out.WeilIs G L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs G' L' k (x ≫ g₁) (y ≫ g₂) c

def WeilEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  ∀ k : ℕ, 0 < k → WeilEqAt k L f₁ f₂ L' g₁ g₂

end Pairings

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Zw (H : Host E) : Subalgebra ℤ (𝓞 E) := Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))

def wz (H : Host E) : Zw H := ⟨H.w0, Algebra.self_mem_adjoin_singleton ℤ H.w0⟩

variable {H : Host E}

structure IsPrincipal {S : Scheme.{0}} (t : SAB H S) : Prop where
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L

def SigAt (H : Host E) (p q : ℕ) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G)
    {k : Type} [Field k] (x : Sp k ⟶ S) (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → LieMult act x τ p) ∧ (τ H.rt ≠ ρ → LieMult act x τ q)

def HasSig (H : Host E) (p q : ℕ) {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (act : OAct (𝓞 E) G)
    (ρ : R) : Prop :=
  ρ ^ 2 = -(H.d : R) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k), SigAt H p q act (spMap β) (β ρ)

def herm (D : Datum H) (x y : D.La) : Zw H :=
  ((D.EF (H.w0 • x) y - D.EF x y : ℤ) : Zw H) + ((D.EF x y : ℤ) : Zw H) * wz H


end GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms
