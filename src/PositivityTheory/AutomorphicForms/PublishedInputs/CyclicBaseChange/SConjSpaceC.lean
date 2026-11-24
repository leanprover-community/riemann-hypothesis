module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.IsGalAd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

def SCuspOf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) sat inf, IsCusp (F := F) n sat inf → ∃ π : Cusp F n, π.sat = sat ∧ π.inf = inf

def SIsCusp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n), IsCusp (F := F) n π.sat π.inf

def SIsoSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π π' : Cusp F n), π.Iso π' → ∀ w B, π.sat w B → π'.sat w B

def STwSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n) (η : HChar F),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ ∀ B, π.sat v B → (π.twist η).sat v (B.map (· * η.val v))

def SSatEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.sat v B

def SSatUniq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n) v B B', π.sat v B → π.sat v B' → B = B'

def SConjSpaceC : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] (σ : M ≃+* M) (s : Ad M ≃+* Ad M), IsGalAd σ s →
    ∀ (n : ℕ) (P : CuspSub M n), ∃ P' : CuspSub M n,
      (Cusp.cx P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space

def SConjSpaceR : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsTotallyReal M] (σ : M ≃+* M) (s : Ad M ≃+* Ad M), IsGalAd σ s →
    ∀ (n : ℕ) (P : UpperTheory.V.TR.CuspSub M n), ∃ P' : UpperTheory.V.TR.CuspSub M n,
      (Cusp.re P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.re P).space

def SConjSatC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [_root_.NumberField.IsTotallyComplex M] (σ : M ≃ₐ[K] M)
    (s : Ad M ≃+* Ad M), IsGalAd σ.toRingEquiv s → ∀ (n : ℕ) (P P' : CuspSub M n),
    (Cusp.cx P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space →
    ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
      (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, (CG.mk P).HasSat (g w) B → (CG.mk P').HasSat w B

def SConjSatR : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsTotallyReal M] (σ : M ≃ₐ[K] M)
    (s : Ad M ≃+* Ad M), IsGalAd σ.toRingEquiv s → ∀ (n : ℕ) (P P' : UpperTheory.V.TR.CuspSub M n),
    (Cusp.re P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.re P).space →
    ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
      (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, P.HasSat (g w) B → P'.HasSat w B

def SNormPow : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f

end UpperTheory.CBC
