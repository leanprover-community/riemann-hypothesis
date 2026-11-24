module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SatIndepOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def InertInSec : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S →
  ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S

def gc (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (c : (Fin n → ℤ) →₀ ℂ) : UL n w → ℂ := fun y =>
  c.sum fun x t => t * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ) * fU n w b ϖ (lOf x) y

def ConeEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
  ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ),
    IsWitt n w b → IsUnifAt ϖ → IsUnramInv (ϖ : w.adicCompletion E) (cj w) q → IsAdmissible σ.ρ → SatUL b ϖ q σ α →
    ∃ ξ : Fin n → ℂˣ, N3.Mono ξ ∧ Finset.univ.val.map ξ = GlobalTheory.LGrp.bcParam n α ∧
      ∃ y : fixed σ.ρ (iwU n w b), y ≠ 0 ∧ ∀ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n 2) →
        PositivityTheory.Rg.BcB.F.Eig.locOp σ (iwU n w b) (gc w b ϖ c) y = evalGL c (chiN w ξ) • y

def ConeEigOf : Prop := EigInert → PositivityTheory.Rg.BcB.F.LemB.BcWeyl → ConeEig

def SatCompAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (σ : SmIrr (UL n w)) (b : GLw n w) (ϖ ϖ' : (w.adicCompletion E)ˣ) (q q' : ℕ)
    (α α' : Fin (n / 2) → ℂˣ), IsCompU π w σ → IsWitt n w b → IsUnifAt ϖ' →
    IsUnramInv (ϖ : w.adicCompletion E) (cj w) q → IsUnramInv (ϖ' : w.adicCompletion E) (cj w) q' →
    HasSatAt π w (cj w) ϖ q α → SatUL b ϖ' q' σ α' → GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α'

end PositivityTheory.Rg.BcB.F.FX

end
