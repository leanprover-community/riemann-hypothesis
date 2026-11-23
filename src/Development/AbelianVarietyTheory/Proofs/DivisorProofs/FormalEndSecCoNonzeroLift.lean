module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_comp {X Y Y' : Scheme.{0}} (c : Y ⟶ Y') (f : Y' ⟶ X) {U : X.Opens} (r : Γ(X, U))
    {y : Y} (h : y ∈ Y.basicOpen ((c ≫ f).app U r)) : c y ∈ Y'.basicOpen (f.app U r) := by
  rw [← Scheme.preimage_basicOpen] at h ⊢
  exact h

theorem secCoNonzero_of_comp {X Y Y' : Scheme.{0}} (L : LB X) {k k' : ℕ} (c : Y ⟶ Y') (u v : Y' ⟶ X)
    (s : H0 L k) (t : H0 L k') (h : SecCoNonzero L (c ≫ u) (c ≫ v) s t) : SecCoNonzero L u v s t := by
  obtain ⟨y, i, i', h1, h2⟩ := h
  exact ⟨c y, i, i', mem_basicOpen_of_comp c u _ h1, mem_basicOpen_of_comp c v _ h2⟩

theorem formalEnd_secCoNonzero_lift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), FormalEnd U.toUnifPre a h' b → ∀ (k k' : ℕ) (s : H0 U.LG.L k) (t : H0 U.LG.L k'), SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s t → ∀ e : ℕ, SecCoNonzero U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s t := by
  intro R _ _ _ _ D A G _ _ _ U a h' b hb k k' s t h0 e
  induction e with
  | zero => exact h0
  | succ e ih =>
    apply secCoNonzero_of_comp U.LG.L (thickMap R (maximalIdeal R) e G)
    have hf : thickMap R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) (e + 1) G).left =
        (fstG (maximalIdeal R) e G).left := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [hf, ← Category.assoc, hb.2.1 e, Category.assoc, hf]
    exact ih

end GlobalTheory.Mum
