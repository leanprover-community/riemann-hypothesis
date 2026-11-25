module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
open NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Mem.Th
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open GlobalTheory.PRep (smoothPart smoothRep IsSmooth IsAdmissible fixed)
open GlobalTheory.Orb (dsRep TypeDataG)
open scoped TensorProduct ComplexConjugate InnerProductSpace

namespace GlobalTheory.AutMult

variable {D : D7} (V : HSp D) {H X W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup X]
  [InnerProductSpace ℂ X] [AddCommGroup W] [Module ℂ W] {S : D.what₂.Tau → SPar}

section Types

variable {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
  {v : HeightOneSpectrum (𝓞 D.host.F)}

variable {V}

def LocContains (τ : Representation ℂ (Kv V v) Z) (σv : Representation ℂ (Gv V v) Y) : Prop :=
  Contains τ (σv.comp (Kv V v).subtype)

def ContainsAt (τ : Representation ℂ (Kv V v) Z) (σ : Representation ℂ (GfC V) W) : Prop :=
  LocContains τ (σ.comp (locFin V v))


variable (v) in
def IsSphericalAt (σ : Representation ℂ (GfC V) W) : Prop := LGrp.IsSpherical (σ.comp (locFin V v)) (Kv V v)

def IsSphericalOff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (σ : Representation ℂ (GfC V) W) : Prop :=
  ∀ v ∉ S, IsSphericalAt v σ

variable {σ : Representation ℂ (GfC V) W} {σv : Representation ℂ (Gv V v) Y} {τ : Representation ℂ (Kv V v) Z}

theorem isSphericalOff_of_fixed {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : LGrp.IsSpherical σ (KOff V S)) :
    IsSphericalOff S σ := fun _ hv =>
  let ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  (Submodule.ne_bot_iff _).2 ⟨x, LGrp.mem_fixed.2 fun _ hk => LGrp.mem_fixed.1 hx _ (emb_mem_levelOff hv hk), h0⟩

end Types

section Mult

variable (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def mDisc (π : GA D V →* (H →L[ℂ] H)) : Cardinal := multIn π (RG V μ) (L2discG V μ)

def mCusp (π : GA D V →* (H →L[ℂ] H)) : Cardinal := multIn π (RG V μ) (L2cusp V μ)



variable {V}

def mDiscDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) : Cardinal :=
  Module.rank ℂ (homFinDS σ M (RG V μ) (L2discG V μ))

def mCuspDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) : Cardinal :=
  Module.rank ℂ (homFinDS σ M (RG V μ) (L2cusp V μ))

variable {μ} {π : GA D V →* (H →L[ℂ] H)} {π' : GA D V →* (X →L[ℂ] X)} {σ : Representation ℂ (GfC V) W}
  {δ : GinfC V →* (X →L[ℂ] X)} {M : DSModel V S}

theorem mCusp_eq_Rcusp : mCusp V μ π = multIn π (Rcusp V μ) ⊤ := (multIn_rep (isSubrep_L2cusp V μ)).symm


open Classical in
theorem mDS_congr {W' : Type} [AddCommGroup W'] [Module ℂ W'] {σ' : Representation ℂ (GfC V) W'} (e : σ.Equiv σ') :
    mDiscDS μ σ M = mDiscDS μ σ' M ∧ mCuspDS μ σ M = mCuspDS μ σ' M := ⟨multTensorPi_congr e, multTensorPi_congr e⟩

end Mult

section Forms

variable (θ : InfF D) (A : CptF V) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def finVec (π : GA D V →* (H →L[ℂ] H)) : Submodule ℂ H := kFinVec (toRep π) (Kinf θ V A) ⊓ smoothPart (finRes π)


omit [μ.IsMulRightInvariant] in
variable {V μ} in
theorem lift_add_ae {F F' : DividedPowerChartLift V μ} {φ ψ : GA D V → ℂ} (e : lift (GQ V) F =ᵐ[μ] φ) (e' : lift (GQ V) F' =ᵐ[μ] ψ) :
    lift (GQ V) (F + F' : DividedPowerChartLift V μ) =ᵐ[μ] φ + ψ :=
  EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')) (e.add e')


omit [μ.IsMulRightInvariant] in
variable {V μ} in
theorem lift_smul_ae (c : ℂ) {F : DividedPowerChartLift V μ} {φ : GA D V → ℂ} (e : lift (GQ V) F =ᵐ[μ] φ) :
    lift (GQ V) (c • F : DividedPowerChartLift V μ) =ᵐ[μ] c • φ :=
  EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)


omit [μ.IsMulRightInvariant] in
def formsIn (𝒜 : Submodule ℂ (GA D V → ℂ)) (U : Submodule ℂ (DividedPowerChartLift V μ)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | φ ∈ 𝒜 ∧ ∃ F ∈ U, lift (GQ V) F =ᵐ[μ] φ}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
  add_mem' := fun ⟨h, F, hF, e⟩ ⟨h', F', hF', e'⟩ => ⟨add_mem h h', _, add_mem hF hF', lift_add_ae e e'⟩
  smul_mem' := fun c _ ⟨h, F, hF, e⟩ => ⟨𝒜.smul_mem c h, _, U.smul_mem c hF, lift_smul_ae c e⟩

variable {V}


variable {θ A μ} {π : GA D V →* (H →L[ℂ] H)} {φ ψ : GA D V → ℂ}



variable {ι ι' : finVec V θ A π →ₗ[ℂ] (GA D V → ℂ)}


end Forms

section Examples

variable (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end Examples

end GlobalTheory.AutMult

end
