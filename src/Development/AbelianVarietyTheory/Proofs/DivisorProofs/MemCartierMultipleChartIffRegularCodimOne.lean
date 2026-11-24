module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ChartHartogs

theorem stalk_normal (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (p : PrimeSpectrum R) :
    IsDomain ((Spec.structureSheaf R).presheaf.stalk p) ∧ IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk p) :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors (R := R) (M := p.asIdeal.primeCompl) (S := (Spec.structureSheaf R).presheaf.stalk p) (hM := p.asIdeal.primeCompl_le_nonZeroDivisors),
    isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors⟩

theorem chart_normal (σ : Setup) (x : Sp σ.R) :
    IsLocallyNoetherian (σ.C x).G.left ∧ ∀ z : (σ.C x).G.left, IsIntegrallyClosed ((σ.C x).G.left.presheaf.stalk z) := by
  have hs : Smooth (σ.C x).G.hom := (σ.C x).semi.smooth
  obtain ⟨h1, h2⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (σ.C x).R
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom, fun z => ?_⟩
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).1
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).2
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth (σ.C x).G.hom z).2

theorem mem_sec_iff : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ) (v : (σ.C x).G.left.functionField), v ∈ Sec (σ.D₁ x) k ↔ (∀ z : (σ.V x).toScheme, (k • σ.D₁ x).RegularAt ((σ.V x).ι z) v) ∧ ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z v := by
  intro σ x k v
  have hV1 : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → (k • σ.D₁ x).IsEqn z 1 := fun z hz => by
    simpa using (σ.noVert x z hz).nsmul k
  constructor
  · intro h
    refine ⟨fun z => h _, fun z hz => ?_⟩
    have := (hV1 z hz).regularAt_iff.1 (h z)
    simpa using this
  · rintro ⟨h1, h2⟩ y
    obtain ⟨hLN, hN⟩ := chart_normal σ x
    obtain ⟨g, hg⟩ := (k • σ.D₁ x).exists_isEqn y
    obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
    refine hg.regularAt_iff.2 (GlobalTheory.Hartogs.regAt_of_forall_dvr _ hN _ y fun z hzy hdvr => ?_)
    have hgz := hU z (hzy.mem_open U.isOpen hyU)
    by_cases hzV : z ∈ σ.V x
    · have := h1 ⟨z, hzV⟩
      rw [Scheme.Opens.ι_apply] at this
      exact hgz.regularAt_iff.1 this
    · have hv : Vert (σ.C x).G.hom (σ.ρ x σ.f) z :=
        ⟨IsDiscreteValuationRing.ringKrullDim_eq_one _, not_not.1 fun h => hzV ((σ.hV x z).2 h)⟩
      exact hgz.regularAt_iff.1 ((hV1 z hv).regularAt_iff.2 (by simpa using h2 z hv))

end GlobalTheory.Desc.ChartHartogs
