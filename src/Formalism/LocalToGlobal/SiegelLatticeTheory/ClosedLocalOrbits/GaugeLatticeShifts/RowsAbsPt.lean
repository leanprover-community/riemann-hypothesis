module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atPt_uniq {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop) (t : TermQ Λ F P)
    (w w' : Point E (r + 1)) (h : AtPt Λ F P t w) (h' : AtPt Λ F P t w') : w = w' := by
  obtain ⟨F₁, ⟨h₁, e₁⟩, -, c₁⟩ := h
  obtain ⟨F₂, ⟨h₂, e₂⟩, -, c₂⟩ := h'
  have hq : Quot.mk (Rel Λ F P) ⟨F₁, h₁⟩ = Quot.mk (Rel Λ F P) ⟨F₂, h₂⟩ := e₁.trans e₂.symm
  have hg := Quot.eqvGen_exact hq
  have inv : ∀ x y : Carrier P, Relation.EqvGen (Rel Λ F P) x y → ∀ v : Point E (r + 1),
      (IsInCell (ZhatOM (ZhatL F x.1)) v ↔ IsInCell (ZhatOM (ZhatL F y.1)) v) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact Formalism.L2.SG.Pf.cell_function_holds Λ F P x y hr
    | refl x => exact fun v => Iff.rfl
    | symm x y _ ih => exact fun v => (ih v).symm
    | trans x y z _ _ ih₁ ih₂ => exact fun v => (ih₁ v).trans (ih₂ v)
  exact Formalism.L2.SG.PtCell.isInCell_uniq ((inv _ _ hg w).1 c₁) c₂

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem ptUniq_holds : PtUniq X Y u u' := fun t w w' h h' => atPt_uniq _ _ _ t.cls w w' h h'

end Formalism.L2.SG.RowsAbsX
