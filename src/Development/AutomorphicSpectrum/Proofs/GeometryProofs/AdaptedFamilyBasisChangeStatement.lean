module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedFamilyBasisChange
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

@[expose] public section

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.adapted_family_basis_change : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab : Ψ → Ψ ⊕ Ψ) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : Ψ → Fin k → A.Λ) (bL : Ψ → Fin m → V) (T : Ψ → Matrix (Fin m) (Fin m) L), IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ (e : L →+* ℂ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) → Function.Injective j → ∀ (ρ' : 𝓞 E →+* Module.End ℂ V'), (∀ a x, ρ' a (j x) = j (A.ρ a x)) → (∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a))) → ∀ hb : V' → V' → ℂ, (∀ τ c c', hb (j (q τ c)) (j (q τ c')) = (A.Bq.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c)) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c'))) → PhiNormSq ρ' hb (A.I.map j) (4 * Real.pi)⁻¹ (fun τ => e.comp (A.σ (lab τ))) (fun τ i => j (bL τ i)) ((((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange.phiNormSq_baseChange | exact GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange.phiNormSq_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange.phiNormSq_baseChange <;> assumption)
