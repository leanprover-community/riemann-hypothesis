module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicitiesGeometricPointsDescend
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lie_multiplicities_geometric_points_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.LieDesc.lieMult_descend | exact GlobalTheory.LieDesc.lieMult_descend | (intros; apply GlobalTheory.LieDesc.lieMult_descend; all_goals assumption)
