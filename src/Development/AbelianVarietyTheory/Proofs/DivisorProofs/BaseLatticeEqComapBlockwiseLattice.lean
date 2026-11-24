module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
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

theorem baseLattice_eq_comap_blockwise_lattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) =
      (blkLat (ι := Fin n' × Fin n) (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 B.lamM))).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  have h0 : TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) = powLat B.lamM (n * 2) (n' * 2) :=
    Lat0 D cc δ
  rw [h0]

  have himg : ∀ x : Fin 4 × D.what₂.Tau → ℂ,
      B.gC x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) ↔
        x ∈ pow4 B.lamM := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := B.gC.injective hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext z
  simp only [AddSubgroup.mem_comap]
  show (∀ i j, (fun τ => z τ i j) ∈ B.lamM) ↔ ∀ k, (fun w => phi B n n' z (k, w)) ∈ _
  have e : ∀ k, (fun w => phi B n n' z (k, w)) = B.gC (blk D k z) := fun k => rfl
  simp only [e, himg]
  constructor
  · intro h k a
    exact h (posE n n' (k, a)).1 (posE n n' (k, a)).2
  · intro h i j
    have := h ((posE n n').symm (i, j)).1 ((posE n n').symm (i, j)).2
    have e2 : slice ((posE n n').symm (i, j)).2 (blk D ((posE n n').symm (i, j)).1 z) = fun τ => z τ i j := by
      funext τ
      show z τ (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).1
        (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).2 = z τ i j
      simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    rw [← e2]; exact this

end GlobalTheory.BaseVacuum
