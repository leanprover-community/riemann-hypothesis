module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
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

@[expose] public section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem charpoly_eq_finsum_psi (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V) :
    s (LinearMap.charpoly g) =
      ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  haveI := Fintype.ofFinite {W : Submodule F V // ∀ x ∈ W, g x ∈ W}
  haveI := Fintype.ofFinite {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}
  let T : {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := ⟨⊤, fun _ _ => Submodule.mem_top⟩
  have hT : psi s T.1 (g.restrict T.2) = psi s V g := by
    rw [← psi_conj F s T.1 V Submodule.topEquiv (g.restrict T.2)]
    congr 1
  rw [finsum_eq_sum_of_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ T), hT, psi_eq,
    finsum_eq_sum_of_fintype]
  rw [sub_add, eq_comm, sub_eq_self, sub_eq_zero]
  refine Finset.sum_bij (fun W _ => ⟨W.1, W.2.2⟩) ?_ ?_ ?_ ?_
  · intro W _
    refine Finset.mem_erase.2 ⟨fun h => W.2.1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a _ b _ h
    exact Subtype.ext (Subtype.mk.inj h)
  · intro b hb
    exact ⟨⟨b.1, fun h => (Finset.mem_erase.1 hb).1 (Subtype.ext h), b.2⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

end GlobalTheory.CuspGL
