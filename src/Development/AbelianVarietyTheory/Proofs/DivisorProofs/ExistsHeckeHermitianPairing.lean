module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory

namespace GlobalTheory.MultPetersson

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem integrableOn_star_mul (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c)
    {f f' : GA D V → ℂ} (hf : Continuous f) (hf' : Continuous f')
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hl' : ∀ γ ∈ GQ V, ∀ g, f' (γ * g) = f' g) :
    IntegrableOn (fun g => star (f g) * f' g) 𝓕 μ :=
  GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V μ 𝓕 C hμ h𝓕 hC hcov _
    ((continuous_star.comp hf).mul hf') (fun γ hγ g => by simp only [hl γ hγ, hl' γ hγ])

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {ι : Type} [Fintype ι] (M : DSModel V S) (w : ι → M.Vec)

end GlobalTheory.MultPetersson

namespace GlobalTheory.MultPetersson


end GlobalTheory.MultPetersson
