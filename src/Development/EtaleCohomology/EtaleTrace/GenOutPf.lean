module

public import Development.EtaleCohomology.EtaleTrace.LCoverCut
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
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOn {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ}
    (w : Fin (N + 1) → X.functionField) (U : X.Opens) (πU : U.toScheme ⟶ PN k N) : Prop :=
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ((⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) w f ≠ 0) ∧
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : (⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f),
      U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ h (πU.app _
          (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))) *
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from
          eval₂ (kHom p) w f) ^ m =
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from eval₂ (kHom p) w g)

def GenOutChart : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField), (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x) →
  ∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

def GenOutGlue : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField),
  (∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU) →
  ∃ π : X ⟶ PN k N, π ≫ PNto k N = p ∧ Gen p π w

theorem GenOut_of (h1 : GenOutChart) (h2 : GenOutGlue) : GenOut := by
  intro k _ X _ p N w hw
  exact h2 k p N w (h1 k p N w hw)

end LateralTheory.EtaleTrace.Cov
