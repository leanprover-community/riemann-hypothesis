module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PairingExtends
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace GlobalTheory.CompanionTheory.Ar.HT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.BT

structure TorsTower (p : ℕ) {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] where

  Γ : ∀ n, QFGroup O (LevGrp La p n)

  i : ∀ n, (Γ n).G.left ⟶ G.left
  tors : ∀ n, (Γ n).IsTorsionAlong G y (p ^ n) (i n)
  compat : ∀ n (a : La), ((Γ n).pt (lev p n a)).left ≫ i n = ((Γ (n + 1)).pt (lev p (n + 1) (p • a))).left ≫ i (n + 1)

namespace TorsTower

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)

def IsDer {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ)
    (f : LevGrp La p n → O) (w : Module.Dual O L) : Prop :=
  ∃ s : Γ((X.Γ n).G.left, ⊤), (X.Γ n).HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))) ⟶ (X.Γ n).G.left,
      v ≫ (X.Γ n).G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (O ⧸ Ideal.span {((p ^ n : ℕ) : O)})
        (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ X.i n = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)}) (w e))

def Induces (u : G ⟶ G) (φ : La →+ La) : Prop :=
  ∀ n (a : La), ((X.Γ n).pt (lev p n (φ a))).left ≫ X.i n = ((X.Γ n).pt (lev p n a)).left ≫ X.i n ≫ u.left

def PairingRegular (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s : Γ(((X.Γ n).G ⊗ (X.Γ n).G).left, ⊤), ∀ a b : La,
    valAt (lift ((X.Γ n).pt (lev p n a)) ((X.Γ n).pt (lev p n b))).left ⊤ le_top s =
      algebraMap O (FractionRing O) ((ζ n ^ B a b : Oˣ) : O)

end TorsTower

end GlobalTheory.CompanionTheory.Ar.HT
