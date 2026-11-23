module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFormVanishesTangentsOfLieBasis
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y → ∀ f : Form (B.hom ≫ 𝟙 (Sp R)), (∀ i, tanVal (y i) f = 0) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (B' : Over (Sp R')) [GrpObj B'] [IsCommMonObj B'] (φ : B'.left ⟶ B.left), IsGrpPullback B' B (spMap σ) φ → ∀ (m : IsMor (dp0 R) (B.hom ≫ 𝟙 (Sp R)) (dp0 R') (B'.hom ≫ 𝟙 (Sp R')) σ φ) (v : epsR R' ⟶ B'), IsTangent v → tanVal v (m.pullForm f) = 0 := by
  first | exact @GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | exact GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | (intros; apply GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis <;> assumption)
