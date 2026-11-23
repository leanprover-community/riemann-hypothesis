module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitive
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (F.X ⟶ F.X)) (ν : Ga → (F.univ.A.left ⟶ F.univ.A.left)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ ν 1 = 𝟙 _ ∧ (∀ a c, ν (a * c) = ν a ≫ ν c) ∧ (∀ a, ρ a ≫ F.s ≫ spMap j = F.s ≫ spMap j) ∧ (∀ a, SRelBy F.univ F.univ (N / n) (N / n) (ρ a) (ν a)) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → ∃ a, y ≫ ρ a = y' := by
  first | exact @GlobalTheory.SiegAct.siegel_group_action | exact GlobalTheory.SiegAct.siegel_group_action | (intros; apply GlobalTheory.SiegAct.siegel_group_action <;> assumption)
