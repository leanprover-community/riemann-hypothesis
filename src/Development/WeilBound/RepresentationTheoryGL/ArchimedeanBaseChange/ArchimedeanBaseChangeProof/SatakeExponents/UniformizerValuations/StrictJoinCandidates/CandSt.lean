module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
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
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

def CandIndep : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T' : Finset (Pl E))
  (c c' : Pl E → (Fin n → ℤ) →₀ ℂ) (e e' : ∀ w : Pl E, GLw n w → ℂ) (b b' : ∀ w : Pl E, GLw n w) i s₁ s₂ Pa Pb D,
  F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D ↔ F₀.Cand (F₀.loc T' c' e' b') i s₁ s₂ Pa Pb D

def CandFin : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ),
  1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T' : Finset (Pl E))
  (c : Pl E → (Fin n → ℤ) →₀ ℂ) (e : ∀ w : Pl E, GLw n w → ℂ) (b : ∀ w : Pl E, GLw n w),
  (∀ w ∈ T', ¬ IsSplitAt w ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) →
  (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
    ∀ s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → w ∈ T' →
      ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
  (∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D →
    ∃ j, (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (Dl j) w)) ∧
      Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) = Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w)) ∧
      FiniteDimensional ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w))) ∧
  ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → ∀ w ∈ T',
    Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 (F₀.C.a i) (n - F₀.C.a i) w)) ≤ m₀

end PositivityTheory.Rg.BcB.F.FX

end
