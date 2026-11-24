module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftExactFunctorRepresentableTorsionModules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory GlobalTheory.SelFun

theorem _root_.GlobalTheory.T.leftExact_functor_representable_torsion_modules : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
  (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
  (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
  Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) → ∀ n : ℕ,
  ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧ (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M ⟶ B, (F.map φ).hom ξ = 0 → φ = 0) ∧
    ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M ⟶ B, (F.map φ).hom ξ = η := by
  first | exact @GlobalTheory.SelFun.Level.level | exact GlobalTheory.SelFun.Level.level | (intros; apply GlobalTheory.SelFun.Level.level <;> assumption)
