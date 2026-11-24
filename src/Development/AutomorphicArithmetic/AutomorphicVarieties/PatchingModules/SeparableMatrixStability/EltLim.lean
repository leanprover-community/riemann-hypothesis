module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.elt_lim :
    ∀ (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (a : ∀ N, Γ N), (∀ N, Function.Surjective (π N)) → ∃ b : B, ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b := by
  intro Ph B _ _ _ _ _ _ Γ _ π πo U a hπ
  choose g hg using fun N => hπ N (a N)
  obtain ⟨b, hb⟩ := (exists_lim_elt Ph ℕ U fun N => (π N).ker).1 g
  refine ⟨πo b, fun V => (hb V).mono fun N h => ⟨g N, b, hg N, rfl, ?_⟩⟩
  simpa using V.toSubgroup.inv_mem h
