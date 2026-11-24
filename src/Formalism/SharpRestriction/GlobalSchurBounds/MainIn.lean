module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Formalism.SharpRestriction.ParConsts
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

namespace Formalism.MainNotions

open Formalism.BasicNotions

def GoodAllFor (Q : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.Induces χ f M → GlobalTheoryTheory.GoodFor Q χ

def Boxes_at (D : D7) (x eps : ℝ) : Prop :=
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir D.host.q) (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir D.host.q a) (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (GlobalTheoryTheory.chDir D.host.d) (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir D.host.d a)
    (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chDir D.host.d a * GlobalTheoryTheory.psDir D.host.q a)
    (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps)
    (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir D.host.d a * GlobalTheoryTheory.psDir D.host.q a) (8 * D.host.q * D.host.d)

def BoxesF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧
    Boxes_at (Fm.D x i) Y eps ∧ GlobalTheoryTheory.BoxE (Fm.D x i) Y eps

def QDRows_at (D : D7) (x eps : ℝ) : Prop :=
  D.host.q.Prime ∧ D.host.q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < D.host.q ∧ (D.host.q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧
  D.host.d.Prime ∧ D.host.d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < D.host.d ∧ (D.host.d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧
  GlobalTheoryTheory.kronSym (-(D.host.d : ℤ)) D.host.q = 1 ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(D.host.d : ℤ)) p = 1) ∧
  Real.log (D.host.QS * D.host.q * D.host.d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def QDRowsF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧ QDRows_at (Fm.D x i) Y eps

def MinkMult (n M : ℕ) : Prop :=
  ∀ H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ), Finite H → Nat.card H ∣ M

def DGamChoice_at (D : D7) : Prop :=
  ∀ M : ℕ, MinkMult (2 * D.R.f * D.R.N D.R.m) M → ∀ u, (D.mem u).C.DGam ∣ M

end Formalism.MainNotions

end
