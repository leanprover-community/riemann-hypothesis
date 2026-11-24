module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
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

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

def LieModel.IsHTFormOver (M : LieModel G ξ E) (N : ℕ) {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)
    (k : R →+* Ω) (w : Module.Dual Ω E) : Prop :=
  ∃ (_ : IsDomain R) (T : Type) (_ : CommGroup T) (Γ : BT.QFGroup R T)
    (i : Γ.G.left ⟶ G.left) (L : Type) (_ : AddCommGroup L) (_ : Module R L)
    (M₀ : LieModel G x L) (j : L → E) (χ : T →* Rˣ) (w₀ : Module.Dual R L),
    Γ.IsTorsionAlong G x N i ∧ (∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left) ∧
      Γ.IsHT i M₀ N χ w₀ ∧ ∀ e, w (j e) = k (w₀ e)

def LieModel.IsHTFormAt (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) (w : Module.Dual Ω E) : Prop :=
  M.IsHTFormOver N (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) (genMap ξ p) w

def LieModel.htLat (M : LieModel G ξ E) (N : ℕ) : Lat ξ (Module.Dual Ω E) := fun p =>
  Submodule.span (regAt ξ p) {w | M.IsHTFormAt N p w}

end GlobalTheory.CompanionTheory.Ar
