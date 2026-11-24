module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
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

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)

noncomputable section

namespace GlobalTheory.TrMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def finFn (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : GfC V → ℂ :=
  fun g => ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v (g : GA D V))

def IsFinMeas (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ν : Measure (GfC V)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∫ g, finFn V ff g ∂ν = ∏ᶠ v, ∫ x, ff v x ∂μf v

def HasTypeVec {V : HSp D} (T : TypeDataG V) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ x : W, x ≠ 0 ∧ (∀ v ∉ T.S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x) ∧
    ∀ v : T.S, x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ}

def SphRest {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : Prop :=
  ∀ v ∉ T.S, v ≠ U.u → ∀ k ∈ Kv V v, ∀ k' ∈ Kv V v, ∀ g, ff v (k * g * k') = ff v g

def IsIrrFam {V : HSp D} {n : ℕ} {W : Fin n → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GfC V) (W i)) : Prop :=
  (∀ i, (σ i).IsIrreducible) ∧ (∀ i, IsAdmissible (σ i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))

def SpecFin : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
      mCuspDS μ σ M < Cardinal.aleph0) ∧
    ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) →
      ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
        (σs : ∀ i, Representation ℂ (GfC V) (Ws i)), IsIrrFam σs ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
          mCuspDS μ σ M ≠ 0 → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i))

def SpecTrace : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs →
      (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
        mCuspDS μ σ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ i, Nonempty (σ.Equiv (σs i))) →
      ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) →
        HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) (∑ i, ((mCuspDS μ (σs i) M).toNat : ℂ) * c i)

def Separation : Prop :=
  ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S →
    ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs → ∀ a : Fin n → ℂ,
      (∀ ff, IsTestFin T U μf ff → SphRest T U ff →
        ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0) →
      ∀ i, HasTypeVec T (σs i) → a i = 0

end GlobalTheory.TrMult

end
