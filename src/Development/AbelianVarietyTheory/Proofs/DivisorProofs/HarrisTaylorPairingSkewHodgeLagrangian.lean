module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.FormFacts
open GlobalTheory.AbDual

theorem formFacts : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → FiniteDimensional k (HdR o₀.A) ∧ 2 * Module.finrank k (Fil o₀.A) = Module.finrank k (HdR o₀.A) ∧ (∀ x y, φ x y = -φ y x) ∧ ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ x y = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ hφ
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  obtain ⟨hfd, hdimH, hdimF⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o₀.A g o₀.ab hg
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab
  have gAB := smooth_prod hg hg
  have C := cupSquare_of_free H.1 hAB gAB
  refine ⟨hfd, by rw [hdimH, hdimF], GlobalTheory.SymmPoincare.skew_of_symm C o₀.isLB (LBIso.symm o₀.symm) hφ, ?_⟩
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 k _ _ hAB gAB o₀.P o₀.isLB ψ hψ
  intro x hx y hy
  have a₁ : push (dp0 k) (𝟙 _) (fst o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) = x := by
    rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl
  have a₂ : push (dp0 k) (𝟙 _) (snd o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) = 0 := by
    rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl
  have b₁ : push (dp0 k) (𝟙 _) (fst o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) = 0 := by
    rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl
  have b₂ : push (dp0 k) (𝟙 _) (snd o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) = y := by
    rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl
  have key : φ x y = ψ (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) := by
    rw [e, a₁, a₂, b₁, b₂]; simp
  rw [key]
  exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)

end GlobalTheory.UPel.HT.FormFacts
