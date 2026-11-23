module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisedIsoCommutesFieldAutomorphismOfTorsion
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.polarisedIso_commutes_fieldAutomorphism_of_torsion : Laws → ∀ (S : Scheme.{0}) (P P' : PolAV S) (C : Type) [Field C] [IsAlgClosed C] (t : Sp C ⟶ S) (φ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (φ.hom ≫ snd (Over.mk t) P'.A).left) → ∀ k : ℕ, 3 ≤ k → (k : C) ≠ 0 → ∀ s : Over.mk t ≅ Over.mk t, (∀ x : Over.mk t ⟶ P.A, x ^ k = 1 → lift (𝟙 (Over.mk t)) (s.hom ≫ x) ≫ φ.hom ≫ snd _ _ = s.hom ≫ lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _) → s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := by
  first | exact @GlobalTheory.SerreTwist.whisker_comp_eq | exact GlobalTheory.SerreTwist.whisker_comp_eq | (intros; apply GlobalTheory.SerreTwist.whisker_comp_eq <;> assumption)
