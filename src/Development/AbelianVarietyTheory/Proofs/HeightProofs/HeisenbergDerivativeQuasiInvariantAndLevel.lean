module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem dRho_quasi_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  intro D ψ V W L f
  refine ⟨fun hf γ w => ?_, fun u hu hf => ?_⟩
  · unfold dRho
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    exact GlobalTheory.DualPairCheck.heis_quasi ψ V W (L t) f hf γ w
  · funext w
    have key : ∀ t, Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) = Heisenberg₂ ψ V W (L t) f := by
      intro t
      conv_rhs => rw [← hf]
      rw [GlobalTheory.DualPairCheck.heis_heis, GlobalTheory.DualPairCheck.heis_heis, (hu t).1, (hu t).2, add_comm]
    have : (fun t => Heisenberg₂ ψ V W (L t) f w) = fun t => Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) w := by
      funext t; rw [key]
    conv_rhs => unfold dRho; rw [this]
    unfold dRho
    rw [Heisenberg₂, ← deriv_const_mul_field]
    rfl

end GlobalTheory.FockCompare
