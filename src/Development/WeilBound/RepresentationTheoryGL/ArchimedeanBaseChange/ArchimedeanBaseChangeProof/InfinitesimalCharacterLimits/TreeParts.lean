module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
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

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Tr.leafList : {N : ℕ} → Tr E N → List (Σ M : ℕ, Submodule ℂ (Sm E M))
  | M, .leaf V _ => [⟨M, V⟩]
  | _, .node t₁ t₂ => t₁.leafList ++ t₂.leafList

def TreeParts {N : ℕ} (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N) : Prop :=
  (List.ofFn fun i => (⟨P.N i, P.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) = t.leafList.filter fun x => 0 < x.1

def rt {a b : ℕ} (g : Hf E a b) (F : H E a b → ℂ) : H E a b → ℂ := fun x => F (x * finH g)

def atW {a b : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)) :
    Hf E a b :=
  (locGL E a w g.1, locGL E b w g.2)

def PreOfTree : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N), t.Good → t.Untw →
  (∀ τ, ∃ m, HasInfCharGL t.space τ m) → ∃ P : PositivityTheory.Rg.BcB.F.Pre E N, TreeParts t P

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
