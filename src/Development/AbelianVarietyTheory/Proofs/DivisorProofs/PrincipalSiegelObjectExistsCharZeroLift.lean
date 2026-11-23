module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalDomainLiftCyclotomicAwayStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPrincipalSymmetricBundleCompleteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSymplecticLevelLiftClosedPointStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLift0

theorem exists_lift_domain : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K]
    (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (βV : cycAway n →+* V) (π : V →+* K)
      (cV : SiegPre g n (zetaAway n) (spMap βV)),
      Function.Injective βV ∧ π.comp βV = β ∧ cV.Principal ∧ SiegPB c cV (spMap π) := by
  intro g n hg hn hodd K _ _ β c hc
  obtain ⟨V, _, _, _, _, βV, π, hV, hinj, hπ, hβ⟩ := GlobalTheory.T.exists_completeLocalDomain_lift_cyclotomicAway n hn K β
  subst hβ
  obtain ⟨AV, _, _, φ, φ₂, PV, hAV, hpb, hsq, hPV, r₁, r₂, hsy, ham, hker, hiso⟩ :=
    GlobalTheory.T.exists_lift_principal_symmetric_bundle_complete K V hV π hπ c.A c.ab c.P c.isLB c.rig₁ c.rig₂ c.symm hc.1 hc.2
  obtain ⟨lev, hadd, htor, hgeom, hcomp⟩ :=
    GlobalTheory.T.exists_unique_symplecticLevel_lift_closedPoint g n hn hodd K V hV βV π hπ c hc AV φ φ₂ PV hAV hpb hsq hPV r₁ r₂ hsy ham hker hiso
  let cV : SiegPre g n (zetaAway n) (spMap βV) :=
    { A := AV, ab := hAV, P := PV, isLB := hPV, rig₁ := r₁, rig₂ := r₂, symm := hsy, lev := lev,
      lev_add := hadd, lev_tors := htor, geom := hgeom }
  exact ⟨V, inferInstance, inferInstance, βV, π, cV, hinj, rfl, ⟨ham, hker⟩, φ, φ₂, hpb, hsq, hiso, hcomp⟩

end GlobalTheory.SiegLift0
