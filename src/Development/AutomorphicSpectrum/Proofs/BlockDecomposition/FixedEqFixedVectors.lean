module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import GroundTheory.AutomorphicForms.SmoothRep
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.AdmDict

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  constructor
  · intro hv h hh
    simpa using hv ⟨h, hh⟩
  · intro hv h
    simpa using hv h h.2

theorem isAdmissible_iff : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ
  have hs : GlobalTheory.PRep.IsSmooth ρ ↔ GroundTheory.Automorphic.IsSmooth ρ := Iff.rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hs.1 h1, fun K hc ho => ?_⟩
    have := h2 K ho hc
    rwa [fixed_eq_fixedVectors] at this
  · rintro ⟨h1, h2⟩
    refine ⟨hs.2 h1, fun K ho hc => ?_⟩
    rw [fixed_eq_fixedVectors]
    exact h2 K hc ho

end GlobalTheory.CompanionTheory.AdmDict
