module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

open scoped BigOperators ComplexConjugate

namespace GlobalTheory.BaseVacuum

theorem gC_sum_conj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, B.gC x w * conj (B.gC y w) = ∑ w, x w * conj (y w) := by
  have hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos_thm B.L).ne'
  have h := B.isomOK x y
  rw [blockFourfold_hOne_eq_hOne] at h
  have e : Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau) = matH (hOne B.L (Fin 4 × D.what₂.Tau)) := rfl
  rw [e] at h
  have h' := h
  simp only [LinearEquiv.coe_coe] at h'
  rw [matH_hOne, matH_hOne] at h'
  exact (div_left_inj' hA).1 h'

theorem phi_isom : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ)
    (z z' : TaylorLogMetric.VC D (n * 2) (n' * 2)),
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z' = stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z') := by
  intro D cc δ B n n' z z'
  have eR : Formalism.L2.Th1.H.stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z')
      = (∑ p, phi B n n' z p * conj (phi B n n' z' p)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := by
    show matH (hOne B.L (Ix D n n')) _ _ = _
    exact matH_hOne _ _ _
  rw [eR]
  have eL : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z'
      = (∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j)) / ((TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) : ℝ) : ℂ) := rfl
  rw [eL, show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  congr 1
  symm
  calc (∑ p, phi B n n' z p * conj (phi B n n' z' p))
      = ∑ k : Fin n' × Fin n, ∑ w, B.gC (blk D k z) w * conj (B.gC (blk D k z') w) := by
        rw [Fintype.sum_prod_type]; rfl
    _ = ∑ k : Fin n' × Fin n, ∑ w, blk D k z w * conj (blk D k z' w) :=
        Finset.sum_congr rfl (fun k _ => gC_sum_conj B (blk D k z) (blk D k z'))
    _ = ∑ p : Ix D n n', blk D p.1 z p.2 * conj (blk D p.1 z' p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j) := ?_
  let e : Ix D n n' ≃ D.what₂.Tau × (Fin (n' * 2) × Fin (n * 2)) :=
    ((Equiv.prodAssoc _ _ _).symm.trans ((posE n n').prodCongr (Equiv.refl _))).trans (Equiv.prodComm _ _)
  rw [Fintype.sum_equiv e (fun p => blk D p.1 z p.2 * conj (blk D p.1 z' p.2))
    (fun q => z q.1 q.2.1 q.2.2 * conj (z' q.1 q.2.1 q.2.2)) (fun p => rfl)]
  simp only [Fintype.sum_prod_type]

end GlobalTheory.BaseVacuum
