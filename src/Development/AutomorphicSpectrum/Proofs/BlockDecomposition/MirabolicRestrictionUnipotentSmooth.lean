module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_toAdd (n : ℕ) :
    Continuous fun x : Multiplicative (Fin n → k) => colMat k n x.toAdd := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast i =>
      have h : Continuous fun a : Multiplicative (Fin n → k) => Multiplicative.toAdd a i :=
        (continuous_apply i).comp continuous_toAdd
      simpa [colMat] using h
  · simpa [colMat, hj] using continuous_const

theorem continuous_unipMir (n : ℕ) : Continuous (unipMir k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_toAdd n)
  · have h : Continuous fun x : Multiplicative (Fin n → k) => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - colMat k n x.toAdd :=
      continuous_const.sub (continuous_colMat_toAdd n)
    exact h

theorem isSmooth_comp_unipMir : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  intro k _ _ _ _ n V _ _ τ h w
  exact (h w).preimage (continuous_unipMir n)

end GlobalTheory.CompanionTheory.MirFourier

end
