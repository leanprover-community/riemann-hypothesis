module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace JacquetFiniteLength₂

variable {n : ℕ} (G : Grp k n)

theorem hasFiniteLength_jacU (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π) (hfl : HasFiniteLength π) :
    HasFiniteLength (jacU G.e π) :=
  (GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff (jacU G.e π) (deltaHalf k _)⁻¹).1
    ((hBZ k).2.1 _ _ _ G.e V π hπ hfl)

end JacquetFiniteLength₂

theorem step_jacFin {n : ℕ} (G : Grp k n) : G.JacquetModuleFiniteProp := by
  intro L V _ _ π hπ hirr
  exact ⟨isSmooth_jacU G.e hπ,
    JacquetFiniteLength₂.hasFiniteLength_jacU G L.loc.bz π hπ (hasFiniteLength_of_isIrreducible hirr)⟩

end Grp

end UpperTheory.TNZ
