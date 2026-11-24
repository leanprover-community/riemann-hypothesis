module

public import Development.EtaleCohomology.EtaleTrace.GenOutPf
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
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def LocOpen : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (z : X.functionField), IsOpen {y : X | z ∈ loc X y}

def ChartMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem GenOutChart_of_cut (h1 : LocOpen) (h2 : ChartMap) : GenOutChart := by
  intro k _ X _ p N w hw x
  obtain ⟨i, hi, hx⟩ := hw x
  have hop : IsOpen {y : X | ∀ j, w j / w i ∈ loc X y} := by
    have : {y : X | ∀ j, w j / w i ∈ loc X y} = ⋂ j, {y : X | w j / w i ∈ loc X y} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => h1 X (w j / w i)
  obtain ⟨πU, h1U, h2U⟩ := h2 k p N w i hi ⟨_, hop⟩ (fun y hy => hy)
  exact ⟨⟨_, hop⟩, πU, hx, h1U, h2U⟩

theorem LocOpen_pf (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : IsOpen {y : X | z ∈ loc X y} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨a, rfl⟩
  obtain ⟨V, hyV, s, rfl⟩ := X.presheaf.exists_germ_eq (x := y) a
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, fun y' hy' => ?_, V.isOpen, hyV⟩
  refine ⟨X.presheaf.germ V y' hy' s, ?_⟩
  simp only [Scheme.algebraMap_germ_eq_germToFunctionField]

def ChartRing : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∀ (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1),
  ∃ φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U),
    ∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m

def ChartGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem ChartMap_pf (h1 : ChartRing) (h2 : ChartGen) : ChartMap := by
  intro k _ X _ p N w i hi U hU
  have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k i)
  obtain ⟨φ, hφ⟩ := h1 k p N w i hi U hU hx
  exact h2 k p N w i hi U hx φ hφ

theorem GenOutChart_of (h1 : ChartRing) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of_cut (fun X _ z => LocOpen_pf X z) (ChartMap_pf h1 h2)

end LateralTheory.EtaleTrace.Cov
