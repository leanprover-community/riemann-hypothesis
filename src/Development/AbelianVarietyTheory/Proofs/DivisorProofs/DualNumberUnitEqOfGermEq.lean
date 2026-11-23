module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
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
public import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualUnitGerm

theorem primeSpectrum_subsingleton (k : Type) [Field k] : Subsingleton (PrimeSpectrum (DualNumber k)) := by
  have key : ∀ p : PrimeSpectrum (DualNumber k), p.asIdeal = maximalIdeal (DualNumber k) := by
    intro p
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    intro x hx
    have hn : IsNilpotent x := by
      rcases TrivSqZeroExt.isUnit_or_isNilpotent x with h | h
      · exact absurd h hx
      · exact h
    exact (nilpotent_iff_mem_prime.1 hn) p.asIdeal p.isPrime
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

theorem unit_eq_of_germ_eq : ∀ (k : Type) [Field k] (z : Sp (DualNumber k)) (u v : (DualNumber k)ˣ), gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn u) = gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn v) → u = v := by
  intro k _ z u v h
  have hs : Subsingleton (Sp (DualNumber k)) := primeSpectrum_subsingleton k
  have h1 : (unitOn u).val = (unitOn v).val := by
    refine TopCat.Presheaf.section_ext (Sp (DualNumber k)).sheaf ⊤ _ _ fun x hx => ?_
    obtain rfl : x = z := Subsingleton.elim _ _
    have := congrArg Units.val h
    rw [gm_val _ x ⊤ hx, gm_val _ x ⊤ hx] at this
    exact this
  exact Units.ext
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv).1 h1)

end GlobalTheory.DualUnitGerm
