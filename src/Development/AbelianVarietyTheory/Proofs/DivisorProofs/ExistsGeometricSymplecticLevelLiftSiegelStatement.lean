module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricSymplecticLevelLiftSiegel
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_geometric_symplectic_level_lift_siegel : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := by
  first | exact @GlobalTheory.SiegGeomLift.exists_geom_level | exact GlobalTheory.SiegGeomLift.exists_geom_level | (intros; apply GlobalTheory.SiegGeomLift.exists_geom_level <;> assumption)
