module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.InstIPSFB
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

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def FrameBoundModuleCondition : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S), MLM.MOk F₀.d₀

def FrameEx0 : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (Pl E), S.card ≤ 1 → Nonempty (Frame0 hR π S)

def FrameEx : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T : Finset (Pl E)),
    Nonempty (RunFrame F₀ T)

def FrameOk : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct

def FrameBound : Prop := ∀ (hR : Rd.ReadLimit) (hD : DiagAlg) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T)
    (h : F.Struct), (F.toGenIn hD h).Bound

def FrameRead : Prop := ∀ (hR : Rd.ReadLimit) (hD : DiagAlg) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T)
    (h : F.Struct), (F.toGenIn hD h).Read

theorem genEx_of (hR : Rd.ReadLimit) (hD : DiagAlg) (h0 : FrameEx0) (h1 : FrameEx) (h2 : FrameOk) (h3 : FrameBound)
    (h4 : FrameRead) : GenEx := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨F₀⟩ := h0 hR E hE n hn π hπ S hS
  refine ⟨F₀.K, F₀.W, F₀.hK, F₀.hW, fun T => ?_⟩
  obtain ⟨F⟩ := h1 hR E hE n hn π hπ S F₀ T
  have h := h2 hR E hE n hn π S T F₀ F
  exact ⟨F.toGenIn hD h, h3 hR hD E hE n hn π hπ S T F₀ F h, h4 hR hD E hE n hn π hπ S T F₀ F h⟩

end PositivityTheory.Rg.BcB.F

end
