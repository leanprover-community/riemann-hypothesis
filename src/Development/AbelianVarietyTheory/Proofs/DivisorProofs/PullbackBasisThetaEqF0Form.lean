module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeBasisCoordinateEqCoordinateEquStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem pullback_basis_theta_eq_F0 : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2)) z = F0 B.L B.ω₀ (Ix D n n') (phi B n n' z) := by
  intro D cc δ B n n' z
  have hth : GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2) = Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) := by
    exact (GlobalTheory.Mem.Col2.JetAlgebraic.thetaZero_periodLattice_eq B _).symm
  simp only [StandardLatticesGL3.pullB, F0, prodFn, hth, GlobalTheory.T.blockVacuum_latticeBasis_coordinate_eq_coordinateEquiv]
  exact Fintype.prod_equiv (ixE D n n') _ _ (fun _ => rfl)

end GlobalTheory.BaseVacuum
