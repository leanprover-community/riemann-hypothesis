module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace P_indDetK

theorem eq_of_eqOn_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (F F' : IndSp (stdBlocks d hd) ρ)
    (h : ∀ κ ∈ KO k (Fin n), F.1.1 κ = F'.1.1 κ) : F = F' := by
  have hfun : F.1.1 = F'.1.1 := by
    funext x
    obtain ⟨p, w, hw, rfl⟩ :=
      GlobalTheory.SmGL.MultiIrr.exists_parab_mul (GlobalTheory.SmGL.stdBlocks d hd) x
    rw [GlobalTheory.SmGL.parInd_law, GlobalTheory.SmGL.parInd_law,
      h w hw]
  exact Subtype.ext (Subtype.ext hfun)

end P_indDetK

theorem step_indDetK : InducedDeterminantTwist := by
  intro k _ _ _ _ s n d hd W _ _ ρ F F' h
  exact P_indDetK.eq_of_eqOn_KO d hd ρ F F' h

end UpperTheory.TNZ
