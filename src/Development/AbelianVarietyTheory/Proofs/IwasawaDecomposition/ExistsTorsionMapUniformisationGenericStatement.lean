module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGeneric
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

theorem _root_.GlobalTheory.T.exists_torsionMap_uniformisation_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : QkPt P.D.toPre F k → (TF (R := R) F ⟶ t.G),
      (∀ q v, GlobalTheory.FlatTors.IsImage P F k q v ↔ v = (f q).left) ∧ (∀ q, f q ^ k = 1) ∧ (∀ x, x ^ k = 1 → ∃ q, f q = x) ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ p p' τ, p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        GlobalTheory.UU.CubWeil t.cub k (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))) ∧
      ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
  first | exact @GlobalTheory.GenTors.exists_torsMap_generic | exact GlobalTheory.GenTors.exists_torsMap_generic | (intros; apply GlobalTheory.GenTors.exists_torsMap_generic <;> assumption)
