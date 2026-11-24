module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChange
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.projBC_holds :
    UpperTheory.Gal.KunnethLefschetz.ProjBC := by
  unfold UpperTheory.Gal.KunnethLefschetz.ProjBC
  refine ⟨?_, ?_⟩
  · intro R R' _ _ φ X p hp
    obtain ⟨N, i, hi, rfl⟩ := hp
    letI : Algebra R R' := φ.toAlgebra
    let s : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R R'))
    let b := GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N
    have H := GroundTheory.Arith.SchemeCoh.ProjSpace.isPullback_baseChange R R' N
    let ι : pullback (i ≫ b) s ⟶ GroundTheory.Arith.SchemeCoh.projectiveSpace R' N :=
      H.lift (pullback.fst (i ≫ b) s ≫ i) (pullback.snd (i ≫ b) s) (by rw [Category.assoc]; exact pullback.condition)
    have hι₁ : ι ≫ _ = pullback.fst (i ≫ b) s ≫ i := H.lift_fst _ _ _
    have hι₂ : ι ≫ _ = pullback.snd (i ≫ b) s := H.lift_snd _ _ _
    have hsq : IsPullback ι (pullback.fst (i ≫ b) s) (GroundTheory.Arith.SchemeCoh.ProjSpace.baseChangeMap R R' N) i := by
      refine IsPullback.of_right (h₂₂ := b) (v₁₃ := s) ?_ hι₁ H.flip
      rw [hι₂]
      exact (IsPullback.of_hasPullback (i ≫ b) s).flip
    exact ⟨N, ι, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hi, hι₂⟩
  · intro R _ X p hp
    obtain ⟨N, i, hi, rfl⟩ := hp
    have : IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N) := inferInstance
    change IsProper (i ≫ GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)
    infer_instance
