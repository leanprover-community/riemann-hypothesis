module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.HTSpecAllHodge
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
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

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.HTSpecB

open GlobalTheory.HTLink

def HTSpecGood : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Formalism.BasicNotions.Loc.FinExt l) (n : ℕ),
    (∀ M : CrystallineSemistableComparison.Model l K.1, M.Sm → (∃ d, SmoothOfRelativeDimension d M.p) → ∃ F : Frame (K := K) M.q n, ∑ a, F.e a = F.d) ∧
    ∃ Φ : ∀ M : CrystallineSemistableComparison.Model l K.1, M.Sm → (∃ d, SmoothOfRelativeDimension d M.p) → ∀ F : Frame (K := K) M.q n, Matrix (Fin F.d) F.Col ℂ_[l],
      (∀ (M : CrystallineSemistableComparison.Model l K.1) (h : M.Sm) (hd : ∃ d, SmoothOfRelativeDimension d M.p) (F : Frame (K := K) M.q n), F.IsHT (Φ M h hd F)) ∧
      ∀ (M M' : CrystallineSemistableComparison.Model l K.1) (h : M.Sm) (h' : M'.Sm) (hd : ∃ d, SmoothOfRelativeDimension d M.p) (hd' : ∃ d, SmoothOfRelativeDimension d M'.p) (F : Frame (K := K) M.q n) (F' : Frame (K := K) M'.q n)
        (u : M'.X ⟶ M.X) (hu : u ≫ M.p = M'.p),
        F.etMat F' (CrystallineSemistableComparison.Model.genMap_q u hu) * Φ M h hd F = Φ M' h' hd' F' * F.hodgeMat F' (CrystallineSemistableComparison.Model.genMap_q u hu)

end CrystallineSemistableComparison.HTSpecB
