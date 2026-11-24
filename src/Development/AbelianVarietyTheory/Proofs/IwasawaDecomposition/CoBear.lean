module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
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

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ}

def Reps {X Y : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (f : Y.X ⟶ X.X) : Prop :=
  (ratOf X).IsHom (ratOf Y) φ f ∧
    (∀ z', ∀ A' ∈ S.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf Y).O z').toSubring (A' * (A.map φ)⁻¹)) ∧
    ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K,
      Par 0 ⊤ h → ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ Bears S φ A h p

theorem Refines.reps {X Y : GlobalTheory.ProjVar.Var F} {Eb : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m}
    {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (h : Refines Eb S φ f) : Reps Eb S φ f :=
  ⟨h.hom, h.sub, h.lifts⟩

def CoBear {X Y₁ Y₂ : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) {K : Type} [Field K] (x : Sp K ⟶ X.X) (p₁ : Sp K ⟶ Y₁.X)
    (p₂ : Sp K ⟶ Y₂.X) : Prop :=
  ∃ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S₁ φ₁ A h p₁ ∧ Bears S₂ φ₂ A h p₂

end GlobalTheory.FlagBundle
