module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedData
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_siegelObject_of_galois_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : X ⟶ Sp o) (sY : Y ⟶ Sp o) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (c : SiegPre h M ζ s) (A₀ : Over Y) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), s = π ≫ sY → IsGaloisCover Ga ρ π → IsAbelianScheme A₀ → IsGrpPullback c.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ a, (c.lev a).left ≫ φ = π ≫ (lev₀ a).left) → ∃ c₀ : SiegPre h M ζ sY, SiegPB c c₀ π := by
  first | exact @GlobalTheory.exists_siegPre_of_galois_descended_data | exact GlobalTheory.exists_siegPre_of_galois_descended_data | (intros; apply GlobalTheory.exists_siegPre_of_galois_descended_data <;> assumption)
