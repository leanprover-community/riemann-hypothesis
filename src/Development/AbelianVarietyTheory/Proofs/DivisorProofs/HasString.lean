module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.GalDef

def wAt {n : ℕ} (lam : DomWeight n) (k : ℕ) : ℤ := if h : k < n then lam.w ⟨k, h⟩ else 0

def IsRunAt {n : ℕ} (lam : DomWeight n) (p t : ℕ) : Prop :=
  p + t ≤ n ∧ (∀ k, p ≤ k → k < p + t → wAt lam k = wAt lam p) ∧ (1 ≤ p → wAt lam p < wAt lam (p - 1)) ∧
    (p + t < n → wAt lam (p + t) < wAt lam p)

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def jumpsOf (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight n) (τ : E →+* Qbar l) : Multiset ℤ :=
  Finset.univ.val.map fun k : Fin n => (k : ℤ) - (lam (ι.toRingHom.comp τ)).w k

def FrobSat (ι : Qbar l ≃+* ℂ) (π : Submodule ℂ (UA E n → ℂ)) (sgn : ℤˣ) (cp : G E Ω → Polynomial (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU π w →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → GlobalTheory.LFun.HasSatGL w σ.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
        cp (g ^ (sgn : ℤ)) = (T.map fun z : ℂˣ =>
          X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod

def HasString (l : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (t : ℕ) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 E), IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ IsUnramU π w ∧
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ) (ν : ℂ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ T ∧ ‖ν‖ = 1 ∧
        (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
          T.map fun z : ℂˣ => (z : ℂ)

end GlobalTheory.GalDef

end
