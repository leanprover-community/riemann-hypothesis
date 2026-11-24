module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
namespace GlobalTheory.MemLoc

theorem _root_.GlobalTheory.MemLoc.exists_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℤ_[l]ˣ,
    ∀ (g : _root_.Formalism.BasicNotions.Loc.GQ l) (m : ℕ) (x : _root_.Formalism.BasicNotions.Loc.Om l), x ^ (l ^ m) = 1 →
      g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val := by
  intro l _
  haveI : ∀ i, HasEnoughRootsOfUnity (_root_.Formalism.BasicNotions.Loc.Om l) (l ^ i) := fun i => by
    unfold _root_.Formalism.BasicNotions.Loc.Om
    infer_instance
  let ρ : _root_.Formalism.BasicNotions.Loc.GQ l →* (_root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) :=
    { toFun := fun g => (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l), map_one' := rfl, map_mul' := fun _ _ => rfl }
  exact ⟨(cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l).comp ρ,
    fun g m x hx => cyclotomicCharacter.spec l (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) x hx⟩

end GlobalTheory.MemLoc
