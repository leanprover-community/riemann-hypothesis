module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvr
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.extend_splitTorus_hom_over_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (G₁ : Over (Sp (FractionRing V))) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left),
    IsGrpPullback G₁ G (spMap (algebraMap V (FractionRing V))) φ₁ → Nonempty (TorusExtension G₁) →
    ∀ (Ω : Type) [Field Ω] (α : FractionRing V →+* Ω) (G' : Over (Sp Ω)) [GrpObj G'] (φ : G'.left ⟶ G.left)
      (h : IsGrpPullback G' G (spMap (α.comp (algebraMap V (FractionRing V)))) φ)
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp Ω) X ⟶ G'), IsMonHom i →
      ∃ j : splitTorus (Sp V) X ⟶ G, IsMonHom j ∧ GlobalTheory.TorusPart.pullTorus h j = i := by
  first | exact @GlobalTheory.TorusPart.extend_torus_hom_dvr | exact GlobalTheory.TorusPart.extend_torus_hom_dvr | (intros; apply GlobalTheory.TorusPart.extend_torus_hom_dvr <;> assumption)
