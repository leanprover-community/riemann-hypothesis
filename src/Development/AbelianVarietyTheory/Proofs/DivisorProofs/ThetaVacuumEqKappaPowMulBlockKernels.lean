module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem thZero_eq_kappa_pow_mul_prod_kerB : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.StdOK →
    ∀ (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)),
      B.thZero (n * 2) (n' * 2) z = B.kappa ^ (n' * n) * ∏ k : Fin n' × Fin n, Formalism.L2.KerInert.kerB B (blk D k z) := by
  intro D cc δ B hS n n' z
  have h4 : tens4 B.thMM = B.kappa • Formalism.L2.KerInert.kerB B := (B.thMM_spec hS).2
  have hk : ∀ k : Fin n' × Fin n,
      B.kappa * Formalism.L2.KerInert.kerB B (blk D k z) =
        ∏ a : Fin 4, B.thMM (fun τ => z τ (posE n n' (k, a)).1 (posE n n' (k, a)).2) := by
    intro k
    have := congrFun h4 (blk D k z)
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have hcard : B.kappa ^ (n' * n) = ∏ _k : Fin n' × Fin n, B.kappa := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [hcard, ← Finset.prod_mul_distrib]
  simp_rw [hk]
  rw [← Fintype.prod_prod_type' (f := fun k a => B.thMM (fun τ => z τ (posE n n' (k, a)).1 (posE n n' (k, a)).2))]
  rw [Fintype.prod_equiv (posE n n')
    (fun p => B.thMM (fun τ => z τ (posE n n' p).1 (posE n n' p).2))
    (fun q => B.thMM (fun τ => z τ q.1 q.2)) (fun _ => rfl)]
  show tensPow B.thMM (n * 2) (n' * 2) z = _
  unfold tensPow
  rw [← Fintype.prod_prod_type' (f := fun i j => B.thMM (fun τ => z τ i j))]

end GlobalTheory.BaseVacuum
