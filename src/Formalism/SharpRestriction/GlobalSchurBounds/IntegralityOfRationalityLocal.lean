module

public import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
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

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.GlobalTheoryTheory

variable (D : D7) (u : D.what₂.Word)


variable {D u} in
def ChiFin0 {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U,
    ((((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)

def FormsTwistCompatibilityFamily : Prop :=
  ∃ (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf), ChiFin0 T

def IntegralityLevelZeroUnderForms : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → LocalLatticeBases.HeckeIntegralLevelZero D u

variable {D u}

variable {eps : ℝ}

theorem hI_tied (Fm : FamP eps) (tie : FamU Fm fun D u => FormsTwistCompatibilityFamily D u ∧ admS D u)
    (hI : ∀ (D : D7) (u : D.what₂.Word), IntegralityLevelZeroUnderForms D u) : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero := by
  obtain ⟨x0, hx0⟩ := tie
  refine ⟨x0, fun x hx hx1 i u hs => ?_⟩
  obtain ⟨hT, hA⟩ := hx0 x hx hx1 i u hs
  exact hI _ _ hT hA hs

end Formalism.MainNotions.RT

end
