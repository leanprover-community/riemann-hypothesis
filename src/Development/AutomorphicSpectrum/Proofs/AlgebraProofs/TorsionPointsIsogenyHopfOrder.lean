module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.TensorSpan

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ _ _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj
  haveI := hj
  have hex : ∀ x : N, ∃ y : N', pt' y = pt x ≫ j := by
    intro x
    apply (hpt'.range _).1
    have hx : (pt x) ^ p = 1 := (hpt.range _).2 ⟨x, rfl⟩
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  choose f hf using hex
  have hadd : ∀ x y : N, f (x + y) = f x + f y := by
    intro x y
    apply hpt'.inj
    rw [hpt'.add, hf, hf, hf, hpt.add, MonObj.mul_comp]
  let jN : N →+ N' :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        simpa using h.symm
      map_add' := hadd }
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  refine ⟨jN, ψ, fun x => hf x, hψ, ?_⟩
  intro g hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨ψ a, ?_⟩
  intro x φ hφ
  have key : spMap (φ.comp ψ) ≫ T'.y = pt' (jN x) := by
    rw [← Chart.spMap_comp ψ φ]
    change (spMap φ ≫ spMap ψ) ≫ T'.y = pt' (f x)
    rw [Category.assoc, hψ, ← Category.assoc, hφ, hf]
  exact ha (jN x) (φ.comp ψ) key
