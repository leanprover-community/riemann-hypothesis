module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.mumfordLambda_bilinear_integral_combinations : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (T : Over (Spec (CommRingCat.of R))) {r : ℕ} (p : Fin r → (T ⟶ D.toPre.P.A)) (m n : Fin r → ℤ), ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (∏ k, p k ^ m k) (∏ l, p l ^ n l)) (fun q : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (p q.1.1) (p q.1.2) q.2)) (Sum.elim Oε (fun q : (Fin r × Fin r) × Fin 4 => -(m q.1.1 * n q.1.2 * Oε q.2)))), t.IsGen ∧ ∀ (ρ : TK R ⟶ T) (y : Fin r → D.toPre.X), (∀ k, ρ ≫ p k = toUnit (TK R) ≫ D.toPre.c (y k)) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t ρ.left z J = (val (D.toPre.tau (∑ k, m k • y k) (∑ l, n l • y l)) (𝟙 _) z J)⁻¹ * ∏ k, ∏ l, val (D.toPre.tau (y k) (y l)) (𝟙 _) z J ^ (m k * n l) := by
  first | exact @GlobalTheory.MumBil.lam_bilin | exact GlobalTheory.MumBil.lam_bilin | (intros; apply GlobalTheory.MumBil.lam_bilin <;> assumption)
