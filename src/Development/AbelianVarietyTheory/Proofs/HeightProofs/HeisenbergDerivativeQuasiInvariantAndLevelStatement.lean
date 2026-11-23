module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeQuasiInvariantAndLevel
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergDerivative_quasiInvariant_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  first | exact @GlobalTheory.FockCompare.dRho_quasi_and_level | exact GlobalTheory.FockCompare.dRho_quasi_and_level | (intros; apply GlobalTheory.FockCompare.dRho_quasi_and_level <;> assumption)
