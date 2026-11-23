module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.G

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Descent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
        (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → IsUnramU σ w) ∧
        (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
        ∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)

def IsOne (D : Pre E n) (π : CuspSub E n) : Prop := D.c = 1 ∧ ∀ i, ∃ e : D.N i = n, e ▸ D.V i = π.V

def SplitLike (D : Pre E n) (π : CuspSub E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

end PositivityTheory.Rg.BcB.G

end
