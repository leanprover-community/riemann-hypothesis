module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

namespace GlobalTheory.GenericSection

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def polyImg (j0 : Fin (N + 1)) (x : Fin N → F) (p : TVar D N) :
    MvPolynomial (SVar D N) F :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) F) j0
    (if p.1 = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (p.1, k)) * C (x k))
    (fun k => X (Sum.inr (p.1, k))) p.2

def freeVar (j0 : Fin (N + 1)) : SVar D N → TVar D N :=
  Sum.elim (fun _ => (0, j0)) (fun q => (q.1, j0.succAbove q.2))

open NumberField MvPolynomial in
variable {F : Type} [Field F] {D N : ℕ} in
theorem _root_.GlobalTheory.GenericSection.polyImg_same (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0) =
      (if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]

open NumberField MvPolynomial in
variable {F : Type} [Field F] {D N : ℕ} in
theorem _root_.GlobalTheory.GenericSection.polyImg_succAbove (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) (k : Fin N) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0.succAbove k) = X (Sum.inr (i, k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]

end GlobalTheory.GenericSection
