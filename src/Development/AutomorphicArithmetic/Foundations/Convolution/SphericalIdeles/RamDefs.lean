module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

def RamSph : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [_root_.NumberField.IsTotallyComplex K]
    [_root_.NumberField.IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      ∀ B, (Cusp.cx π).sat (w.under (𝓞 K)) B → (Cusp.cx P).sat w B

def NormRam : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      normV w = normV (w.under (𝓞 K)) ∧ (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w) ∧
        ∀ η : HChar K, IsNormChar M η → ¬ η.UnrAt (w.under (𝓞 K))

def Unlinked : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K)) B,
    (Cusp.cx π).sat v B → ∀ a ∈ B, ∀ b ∈ B, (a : ℂ) ≠ (Ideal.absNorm v.asIdeal : ℂ) * b

structure IsLiftUnr {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
    [Algebra K M] {a : ℕ} (π : CuspSub K a) (P : CuspSub M a) : Prop where
  weak : WeakBC (CG.mk π).HasSat (CG.mk P).HasSat
  sat : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (B : Multiset ℂˣ), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
    normV w = normV (w.under (𝓞 K)) ^ f → (CG.mk π).HasSat (w.under (𝓞 K)) B → (CG.mk P).HasSat w (B.map (· ^ f))
  inf : ∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))
  loc : SplitLift (Cusp.cx π) (Cusp.cx P)

def LiftUnr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub K a,
    (∀ η : HChar K, IsNormChar M η → (CG.mk π).twist η ≠ CG.mk π) → ∃ P : CuspSub M a, IsLiftUnr π P

def QuadLiftUnr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub K a,
    (∃ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 K)) B) →
    ∃ P : CuspSub M a, IsLiftUnr π P

end UpperTheory.ConvolutionTheory.Sph
