module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut
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
import Mathlib.Tactic.Linter.Style
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
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

theorem LeafSurjGeo_of : LeafSurjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T t
  let F : Bool → Scheme.{0} := fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b
  let m : ∀ b, F b ⟶ T := fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b
  have hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : t.base x ∈ (U : Set X)
      · refine ⟨true, ?_⟩
        show x ∈ Set.range (t ⁻¹ᵁ U).ι.base
        rw [Scheme.Opens.range_ι]; exact hx
      · rw [hU, Set.notMem_compl_iff] at hx
        obtain ⟨z, hz⟩ := hx
        have hw : f.base (ι'.base z) = ι.base z := by
          rw [← Scheme.Hom.comp_apply, hp.w]; simp
        obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z)
          (by rw [hw, hz])
        exact ⟨false, p, hp1⟩
    · cases b <;> dsimp [m] <;> infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows F m),
    Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  intro V g hg
  obtain ⟨W, h, k, hk, rfl⟩ := hg
  obtain ⟨b⟩ := hk
  cases b
  · right
    refine ⟨h ≫ pullback.snd t f, ?_⟩
    simp only [m, Category.assoc, ← pullback.condition]
  · left
    refine ⟨h ≫ (t ∣_ U), ?_⟩
    simp only [m, Category.assoc, morphismRestrict_ι]

end LateralTheory.CohomologicalPurity
