module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
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
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private noncomputable abbrev evF (p : ℕ) (W : Scheme.{0}) : Spc ⥤ Type :=
  ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p))) ⋙
    ((evaluation Scheme.{0}ᵒᵖ Type).obj (op W))

theorem UpperTheory.mem_pullbackImage_iff_factors_through_open :
    ∀ {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (p : ℕ) (W : Scheme.{0}) (z : Sx E p W), ((Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z ↔ ∃ w : W ⟶ U.toScheme, w ≫ U.ι = under π z) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ W), under π (z.res g) = g ≫ under π z) ∧ ∀ (r : ℕ) (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk p), under π (z.along θ) = under π z := by
  intro X U E π p W z
  have hpb : IsPullback ((evF p W).map (pullback.fst π (sch.map U.ι)))
      ((evF p W).map (pullback.snd π (sch.map U.ι))) ((evF p W).map π)
      ((evF p W).map (sch.map U.ι)) := (IsPullback.of_hasPullback π (sch.map U.ι)).map (evF p W)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(evF p W).map (pullback.snd π (sch.map U.ι)) y, ?_⟩
    exact (ConcreteCategory.congr_hom hpb.w y).symm
  · rintro ⟨w, hw⟩
    obtain ⟨y, hy, -⟩ := Types.exists_of_isPullback hpb z (show Sx (sch.obj U.toScheme) p W from w) hw.symm
    exact ⟨y, hy⟩
  · intro V g
    exact ConcreteCategory.congr_hom ((π.app (op (SimplexCategory.mk p))).naturality g.op) z
  · intro r θ
    exact congrFun (congrArg (fun t => t.app (op W)) (π.naturality θ.op)) z
