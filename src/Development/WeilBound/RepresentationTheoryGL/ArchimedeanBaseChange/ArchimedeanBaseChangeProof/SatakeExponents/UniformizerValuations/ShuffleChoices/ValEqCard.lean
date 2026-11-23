module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ShufStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Choice

namespace StandardSymmetricSums

def loF (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def hiF (n : ℕ) (i : Fin (n / 2)) : Fin n := ⟨n - 1 - i.val, by have := i.isLt; omega⟩

theorem lOf_eq {n : ℕ} (x : Fin n → ℤ) (i : Fin (n / 2)) : lOf x i = x (loF n i) - x (hiF n i) := rfl

end StandardSymmetricSums

open StandardSymmetricSums

theorem coneTwo : ConeTwo := by
  intro n x _ hx
  have hx' : ∀ p q : Fin n, p < q → x q + 2 ≤ x p := hx
  unfold Cone
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hi' := i.isLt; have hj' := j.isLt
    rw [lOf_eq, lOf_eq]
    have c1 : loF n i < loF n j := show i.val < j.val by omega
    have c4 : hiF n j < hiF n i := show n - 1 - j.val < n - 1 - i.val by omega
    have := hx' _ _ c1; have := hx' _ _ c4; linarith
  · have hi' := i.isLt
    rw [lOf_eq]
    have c : loF n i < hiF n i := show i.val < n - 1 - i.val by omega
    have := hx' _ _ c; linarith

end PositivityTheory.Rg.BcB.F.Choice

end
