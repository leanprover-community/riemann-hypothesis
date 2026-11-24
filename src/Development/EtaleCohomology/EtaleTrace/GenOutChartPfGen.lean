module

public import Development.EtaleCohomology.EtaleTrace.GenOutChartPf
public import Development.EtaleCohomology.EtaleTrace.GenOutChartPfSect
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def chartMor {k : Type} [Field k] {X : Scheme.{0}} {N : ℕ} (i : Fin (N + 1)) (U : X.Opens)
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
    (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)) :
    U.toScheme ⟶ PN k N :=
  U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)) ≫
    Proj.awayι _ (MvPolynomial.X i) hx zero_lt_one

def ChartOverK : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  chartMor i U hx φ ≫ PNto k N = U.ι ≫ p

def ChartGenOn : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  GenOn p w U (chartMor i U hx φ)

theorem ChartGen_of (h1 : ChartOverK) (h2 : ChartGenOn) : ChartGen := by
  intro k _ X _ p N w i hi U hx φ hφ
  exact ⟨chartMor i U hx φ, h1 k p N w i hi U hx φ hφ, h2 k p N w i hi U hx φ hφ⟩

theorem GenOutChart_of_two (h1 : ChartOverK) (h2 : ChartGenOn) : GenOutChart :=
  GenOutChart_of_gen (ChartGen_of h1 h2)

end LateralTheory.EtaleTrace.Cov
