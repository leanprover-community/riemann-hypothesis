module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lieLattice_localization_modelLieAlgebra : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  first | exact @GlobalTheory.CM.LieLoc.lieLat_localization | exact GlobalTheory.CM.LieLoc.lieLat_localization | (intros; apply GlobalTheory.CM.LieLoc.lieLat_localization <;> assumption)
