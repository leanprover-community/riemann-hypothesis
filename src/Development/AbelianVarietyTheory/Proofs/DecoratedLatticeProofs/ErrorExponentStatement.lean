module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll

@[expose] public section

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.MixPer GlobalTheory.MixModel MeasureTheory
  GlobalTheory.Core.Mi Formalism.L2.SG.InstExistsPf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Matrix

noncomputable section

namespace GlobalTheory.Core.Mi.PerCmp

variable {D : D7} {X : HidaSetting.HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word}
  {V₀ A L : HSp D} {d : HypDec (D.sp.Y 0) V₀ D.R.rS} {o : OrthDec V₀ A L}
  {ζ : Fin L.rank → D.host.E} {lam : D.host.E}

theorem hyp_linIndep {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    LinearIndependent D.host.E d.e.transpose := by
  have h1 : Function.Injective d.e.mulVec := by
    intro x y hxy
    have := congrArg (fun v => (d.e'.conjTranspose * HSpace.gram S).mulVec v) hxy
    simpa [Matrix.mulVec_mulVec, d.e'e] using this
  exact Matrix.mulVec_injective_iff.mp h1

theorem besPer_domN {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) {ψ : AddChar (AF ↥D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (θ : D.host.E) (μ 𝓕) (ν : Measure (flagN d)) (hν : ν.IsHaarMeasure) {𝓝 𝓝' : Set (flagN d)}
    (h𝓝 : IsFundamentalDomain (NFlagQ S d.e) 𝓝 ν) (h𝓝' : IsFundamentalDomain (NFlagQ S d.e) 𝓝' ν)
    (φ : GA D A → ℂ) (f : GA D S → ℂ) (hf : ∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) :
    besPer ψ θ d o ζ μ 𝓕 ν 𝓝 φ f = besPer ψ θ d o ζ μ 𝓕 ν 𝓝' φ f := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : Countable (NFlagQ S d.e) := by
    have hinj : Function.Injective
        (fun x : NFlagQ S d.e => (⟨x.1.1, x.2⟩ : GQ S)) := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ S => z.1) hxy))
    exact hinj.countable
  unfold besPer
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine h𝓝.setIntegral_eq h𝓝' fun γ n => ?_
  have hγ : ((γ : flagN d) : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 γ.2
  change besFun ψ θ d o ζ φ f a ((γ : flagN d) * n) = _
  simp only [besFun, Subgroup.coe_mul]
  rw [psiBes_mul d ψ θ _ γ.1.2 n.2, GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ _ hγ, one_mul,
    mul_assoc ((γ : flagN d) : GA D S), hf _ hγ]

theorem besPer_domA {ρ : ℕ} (B : GlobalTheory.Unf.BesLev D ρ) {ψ : AddChar (AF ↥D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {𝓕 : Set (GA D B.A)} (h𝓕 : IsFundamentalDomain (GQ B.A) 𝓕 B.vA.μ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) :
    besPer ψ 1 B.d B.o B.ζ B.vA.μ 𝓕 B.vN.ν B.vN.𝓝 φ f = B.per ψ φ f := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  exact h𝓕.setIntegral_eq B.vA.fund fun γ x => Shift.inner_left B ψ hψ φ f hφ hf γ.2 x

end GlobalTheory.Core.Mi.PerCmp
