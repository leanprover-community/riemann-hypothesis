module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj {F : Type} [Field F]
    (s : F[X] → ℂ) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V']
      [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
      _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V' (e.conj g) =
        _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e g
    rw [_root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ,
      e.charpoly_conj]
    congr 1
    let σ : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} ≃
        {W : Submodule F V' // W ≠ ⊤ ∧ ∀ x ∈ W, e.conj g x ∈ W} :=
      (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv fun W => by
        change _ ↔ (Submodule.orderIsoMapComap e W ≠ ⊤ ∧
          ∀ y ∈ W.map (e : V →ₗ[F] V'), e.conj g y ∈ W.map (e : V →ₗ[F] V'))
        refine and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩
        · exact ((Submodule.orderIsoMapComap e).injective.ne_iff' (map_top _)).symm
        · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
          simpa [LinearEquiv.conj_apply] using
            Submodule.mem_map_of_mem (f := (e : V →ₗ[F] V')) (h x hx)
        · have := h (e x) (Submodule.mem_map_of_mem hx)
          simpa [LinearEquiv.conj_apply, Submodule.mem_map_equiv] using this
    rw [← finsum_comp_equiv σ]
    refine finsum_congr fun W => ?_
    rw [← ih W.1 (W.1.map (e : V →ₗ[F] V')) (e.submoduleMap W.1)]
    show _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n (W.1.map (e : V →ₗ[F] V')) _ = _
    congr 1


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.psi_conj (F : Type) [Field F]
    (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (e : V ≃ₗ[F] V') (g : Module.End F V) :
    _root_.GlobalTheory.CuspGL.psi s V' (e.conj g) =
      _root_.GlobalTheory.CuspGL.psi s V g := by
  unfold _root_.GlobalTheory.CuspGL.psi
  rw [← e.finrank_eq]
  exact _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj s _ V V' e g

end GlobalTheory.CuspGL
