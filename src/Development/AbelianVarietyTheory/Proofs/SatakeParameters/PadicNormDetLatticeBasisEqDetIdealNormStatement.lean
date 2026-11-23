module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormDetLatticeBasisEqDetIdealNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem _root_.GlobalTheory.T.padic_norm_det_lattice_basis_eq_det_ideal_norm : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (N : ℕ) (L0 L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (B : Matrix (Fin N) (Fin N) ℂ_[p]), (∀ x, x ∈ L0 ↔ ∀ k, IsIntegral ℤ (x k)) → B.det ≠ 0 → (∀ x ∈ L, ∀ a, ‖(B⁻¹.mulVec fun i => tauEmb D lam τ (x i)) a‖ ≤ 1) → (∀ a, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (x : Fin n → Fin N → D.host.E), (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k, x k ∈ L) ∧ ∀ i, B i a = ∑ k, r k * tauEmb D lam τ (x k i)) → ‖B.det‖ = nrmId D lam τ (detId D L0 L) := by
  first | exact @GlobalTheory.DetBasisNorm.norm_det_eq_nrmId | exact GlobalTheory.DetBasisNorm.norm_det_eq_nrmId | (intros; apply GlobalTheory.DetBasisNorm.norm_det_eq_nrmId <;> assumption)
