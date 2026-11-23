module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced

@[expose] public section

noncomputable section

namespace GlobalTheory.ModelRelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModelCompare GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Dominates

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O')
  (hb : β'.comp b = β)

end Dominates

section Dense

variable (Y : Model Xo c β)

theorem densePart (h : IsDedFrac β) : IsLocallyNoetherian Y.X ∧ IsReduced Y.X ∧ Y.X.IsSeparated ∧
    IsPreimmersion Y.j ∧ Flat Y.j ∧ IsDominant Y.j ∧ QuasiCompact Y.j := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := h
  letI := β.toAlgebra
  obtain ⟨h₁, -, h₂, h₃⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x ↦
    have := (Y.normal x).1
    inferInstance
  exact ⟨h₁, isReduced_of_isReduced_stalk Y.X, h₂, h₃⟩

end Dense

section Transition

variable {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O₂ : Type} [CommRing O₂] {β₂ : O₂ →+* c₂.F}
  (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (hl : l.Dvd l₂) (hF : c.F ≤ c₂.F) (b : O →+* O₂)
  (hb : β₂.comp b = (IntermediateField.inclusion hF).toRingHom.comp β) (π : Y₂.X ⟶ Y.X)

end Transition

section Algebra

end Algebra

section Action

variable (Y : Model Xo c β)

variable {Y}

variable (Y)

end Action

end GlobalTheory.ModelRelCompare
