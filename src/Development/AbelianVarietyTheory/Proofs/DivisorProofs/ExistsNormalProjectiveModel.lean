module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CommonModel


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.CommonModel.isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s) : IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.CommonModel.exists_common {R : Type} [CommRing R] {Y W₀ : Scheme.{0}}
    (s₀ : W₀ ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s₀) (i₀ : Y ⟶ W₀)
    {ι : Type} (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (f : ∀ i, Y ⟶ P i)
    (hp : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = i₀ ≫ s₀) (S : Finset ι) :
    ∃ (W : Scheme.{0}) (h : Y ⟶ W) (r : W ⟶ W₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (r ≫ s₀) ∧ h ≫ r = i₀ ∧
      ∀ i ∈ S, ∃ g : W ⟶ P i, h ≫ g = f i ∧ g ≫ p i = r ≫ s₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨W₀, i₀, 𝟙 W₀, by simpa using hs₀, by simp, by simp⟩
  | insert j S _ ih =>
    obtain ⟨W, h, r, hr, hhr, hg⟩ := ih
    have hc : h ≫ (r ≫ s₀) = f j ≫ p j := by
      rw [← Category.assoc, hhr, hf]
    refine ⟨pullback (r ≫ s₀) (p j), pullback.lift h (f j) hc, pullback.fst _ _ ≫ r, ?_, ?_, ?_⟩
    · rw [Category.assoc]
      exact _root_.GlobalTheory.ProjSpace.isProjOver_pullback hr (hp j)
    · rw [← Category.assoc, pullback.lift_fst, hhr]
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨pullback.snd _ _, pullback.lift_snd _ _ _, ?_⟩
        rw [Category.assoc, ← pullback.condition]
      · obtain ⟨g, hg₁, hg₂⟩ := hg i hi
        refine ⟨pullback.fst _ _ ≫ g, ?_, ?_⟩
        · rw [← Category.assoc, pullback.lift_fst, hg₁]
        · rw [Category.assoc, hg₂, Category.assoc]

end GlobalTheory.CommonModel
