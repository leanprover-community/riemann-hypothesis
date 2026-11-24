module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

def cupPowC (A : C ⥤ CommAlgCat.{0} R) (z : CH.Cn (CH.modF A) 2) : ∀ k : ℕ, CH.Cn (CH.modF A) (2 * k)
  | 0 => fun s => (1 : A.obj (s.obj (Fin.last _)))
  | k + 1 => (CH.mulP A).cupC (by omega) (cupPowC A z k) z

def cupListC (A : C ⥤ CommAlgCat.{0} R) : ∀ {k : ℕ}, (Fin k → CH.Cn (CH.modF A) 1) → CH.Cn (CH.modF A) k
  | 0, _ => fun s => (1 : A.obj (s.obj (Fin.last _)))
  | k + 1, ℓ => (CH.mulP A).cupC (by omega) (cupListC A fun i => ℓ (Fin.castSucc i)) (ℓ (Fin.last k))

def resB (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    CH.Cn (CH.modF (V.ι ⋙ A)) k :=
  fun σ => b (σ ⋙ ObjectProperty.ιOfLE h)

theorem capS_le_univ {ι : Type} [Fintype ι] (U : ι → ObjectProperty C) (i : ι) : capS U Finset.univ ≤ U i :=
  fun _ hT => hT i (Finset.mem_univ i)

theorem capS_univ_le {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → ObjectProperty C) (S : Finset ι) :
    capS U Finset.univ ≤ capS U S :=
  fun _ hT α _ => hT α (Finset.mem_univ α)

end CrystallineSemistableComparison.Pb
