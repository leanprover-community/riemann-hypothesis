module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprime
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

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  first | exact @GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | exact GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | (intros; apply GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime <;> assumption)
