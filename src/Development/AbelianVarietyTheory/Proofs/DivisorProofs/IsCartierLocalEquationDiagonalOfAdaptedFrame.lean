module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicMatrixFamilyDiagIsUnitStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem isEqn_diag_of_frame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) (m : ι → ℕ) (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ (y : Y.X), ∀ A ∈ E'.S y, Par m ⊤ (B * A⁻¹) ∧ ∀ x : Root m, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t := by
  intro F _ Y ι m E' gr B hB H y A hA
  have par : ∀ {z : Y.X} {A : Mat m Y.Fn}, A ∈ E'.S z → Par m ⊤ (B * A⁻¹) := fun {z A} h =>
    ((Fr.mem_iff (Fr.mem_genericPoint h)).1 hB).mono le_rfl le_top
  refine ⟨par hA, fun x => ?_⟩
  obtain ⟨A', hA', t', ht', heq⟩ := H y x
  have hP : Par m ((ratOf Y).O y).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have e : B * A⁻¹ = (B * A'⁻¹) * (A' * A⁻¹) := by
    rw [← mul_assoc, mul_assoc B, Mat.inv_mul (Fr.det_ne hA'), mul_one]
  obtain ⟨hu0, hui, -, -⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn _ (A' * A⁻¹) hP x
  obtain ⟨-, -, -, hmul⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn ⊤ (B * A'⁻¹) (par hA') x
  obtain ⟨ht0, -⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn ⊤ (B * A⁻¹) (par hA) x
  have hd : (B * A⁻¹) x.1 x.2 x.2 = t' * (A' * A⁻¹) x.1 x.2 x.2 := by
    rw [e, hmul _ (hP.mono le_rfl le_top), ht']
  refine ⟨Units.mk0 _ ht0, rfl, heq.iff_unitAt.2 ?_⟩
  have hu : UnitAt y ((A' * A⁻¹) x.1 x.2 x.2) := (unitAt_iff hu0).2
    ⟨mem_O_ratOf.1 ((hP x.1).1 x.2 x.2), mem_O_ratOf.1 hui⟩
  convert hu using 1
  rw [Units.val_mk0, hd]
  exact mul_div_cancel_left₀ _ t'.ne_zero

end GlobalTheory.FlagPush
