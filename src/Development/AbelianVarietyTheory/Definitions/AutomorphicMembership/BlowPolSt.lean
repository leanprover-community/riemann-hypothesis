module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
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

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

section Fun

variable {O : Type} [CommRing O]

def resInt (O : Type) [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := by
    rw [φ.eval_eq (n := 0) (r := 0) fun a => ⟨0, Subsingleton.elim _ _⟩]
    exact φ.zero _

def IsTame (φ : InvFun O) : Prop :=
  (∀ (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
    ∀ n B, 0 ≤ φ.toFun n B

end Fun

section Cones

variable {R : Type} [CommRing R] [IsDomain R]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Refines (H : Host E) (q : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) : Prop :=
  IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ IsTwInv H φ ∧ IsPosFn H φ ∧ IsTame φ ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
        (resInt (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ

end Cones

end GlobalTheory.TorRef
