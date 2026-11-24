module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType

namespace GlobalTheory.CompRat

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def wC (H : Host E) (s : ℤ × ℤ) : ℂ := s.1 + s.2 * ((1 + H.rt0) / 2)

def wE (H : Host E) (s : ℤ × ℤ) : 𝓞 E := s.1 + s.2 * H.w0

structure Curve (H : Host E) : Type 1 where
  P : Out.PolAV (Sp ℂ)
  g_eq : P.g = 1
  u : HolUnif P.A P.L P.g
  theta : IsThetaUnif u
  c : ℂ
  c_ne : c ≠ 0
  lat : IsQuadLattice u.Λ H.d c

variable {H : Host E}

def Curve.pt (C : Curve H) (z : ℂ) : Sp ℂ ⟶ C.P.A.left := (C.u.ex fun _ => C.c * z).left

def Curve.ActsBy (C : Curve H) (τ : ℂ ≃+* ℂ) (ι : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ) : Prop :=
  IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) ι ∧
    ∀ a : ℤ × ℤ, C.pt (wC H s * wC H a / n) ≫ ι = spMap (τ : ℂ →+* ℂ) ≫ C.pt (wC H a / n)

def FixesCurve (H : Host E) (τ : ℂ ≃+* ℂ) (n : ℕ) : Prop := ∃ (C : Curve H) (ι : _), C.ActsBy τ ι n (1, 0)

def CurveOver (H : Host E) (F : IntermediateField ℚ ℂ) (n : ℕ) : Prop :=
  ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F, τ x = x) → FixesCurve H τ n

def IsSplit {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : Prop :=
  lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤

def SplitLat (D : Datum H) : Prop :=
  ∃ Lp Lm : Submodule (𝓞 E) D.La, Lp ⊔ Lm = ⊤ ∧ (∀ a ∈ Lp, ∀ b ∈ Lm, D.EF a b = 0) ∧
    Module.finrank (𝓞 E) Lp = D.p ∧ Module.finrank (𝓞 E) Lm = D.q ∧
    (∀ a ∈ Lp, a ≠ 0 → 0 < H.rt0.im * D.EF (H.rt • a) a) ∧ ∀ a ∈ Lm, a ≠ 0 → H.rt0.im * D.EF (H.rt • a) a < 0

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

def ConjugationPermutesPeriods (F : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) (π : Fin F.n → Fin F.n) : Prop :=
  ∀ i P, IsPeriod (F.Di i) ty P →
    ∃ P', IsPeriod (F.Di (π i)) ty P' ∧ spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u (π i) P'

end GlobalTheory.CompRat
