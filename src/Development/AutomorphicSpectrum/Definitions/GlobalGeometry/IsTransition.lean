module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
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

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def tauE {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : E →+* c.F := (τ.codRestrict c.F.toSubfield (c.conj τ) :)

def IsLocBasis (O : Type) [CommRing O] {M : Type} [AddCommGroup M] [Module O M] (p : ℕ) {I : Type} (x : I → M) : Prop :=
  LinearIndependent O x ∧ ∃ n : ℕ, ¬ p ∣ n ∧ ∀ y, n • y ∈ Submodule.span O (Set.range x)

def gramE (D : Datum H) {I : Type} (x : I → D.La) : Matrix I I E := Matrix.of fun m n => sesq D (x m) (x n)

def IsTransition (D : Datum H) {I : Type} [Fintype I] (x e : I → D.La) (T : Matrix I I E) : Prop :=
  ∀ m y, sesq D (x m) y = ∑ n, T m n * sesq D (e n) y

def sgnRt (H : Host E) (b : Bool) : ℂ := if b then H.rt0 else -H.rt0

def IsPure {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {p q : ℕ}
    (x : Fin p ⊕ Fin q → D.La) : Prop :=
  (∀ a, x (.inl a) ∈ PureType.lat hP (sgnRt H true)) ∧ ∀ j, x (.inr j) ∈ PureType.lat hP (sgnRt H false)

end GlobalTheory.CompanionTheory.Ar.Fl
