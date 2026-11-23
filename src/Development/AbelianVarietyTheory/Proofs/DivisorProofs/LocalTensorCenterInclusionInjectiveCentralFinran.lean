module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem iotaF_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  intro p _ G v
  haveI : IsSimpleRing G.C := G.simpleC
  haveI : Nontrivial G.C := inferInstance
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  refine ⟨?_, ?_, ?_⟩
  · have hf : Function.Injective ((IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap) :=
      (algebraMap G.F G.C).injective
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf
    exact this
  · intro z x
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _)]; exact ha.add_left hb
    | tmul a f =>
      induction x using TensorProduct.induction_on with
      | zero => exact Commute.zero_right _
      | add c d hc hd => exact hc.add_right hd
      | tmul b c =>
        rw [iotaF_tmul]
        show (a ⊗ₜ[ℚ] algebraMap G.F G.C f) * (b ⊗ₜ[ℚ] c) = (b ⊗ₜ[ℚ] c) * (a ⊗ₜ[ℚ] algebraMap G.F G.C f)
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm a b,
          Algebra.commutes]
  · rw [Module.finrank_baseChange, Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C,
      G.rankC, mul_comm]

end GlobalTheory.OrbFinAf
