module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeSmoothVariationAlongBoundedUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeveStatement
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
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_decay_step : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a ψ hψ t ht i j hij Ω hΩ
  have hL : {k | finRep E a k ψ = ψ} ∈ nhds (1 : GL (Fin a) (Af E)) :=
    hψ.1.level.mem_nhds (by simp)
  obtain ⟨R, hR0, hcov⟩ := GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level E a (j : ℕ) _ hL
  obtain ⟨Ω', B, C, hΩ', hC, hvar⟩ := GlobalTheory.T.siegelCone_smooth_variation_along_bounded_unipotent E a t ht i j hij Ω hΩ R hR0
  refine ⟨Ω', B, C, hΩ', hC, fun r d hr hrt hd M hM hY c hc => ?_⟩
  refine GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation E a ψ hψ (j : ℕ) (by omega) j.2 (infGL E a (d * c)) (C * (r j / r i) * M) fun x => ?_
  obtain ⟨ξ, z, k, hk, hz, hx⟩ := hcov x
  have hk' : finRep E a k ψ = ψ := hk
  have e : ψ.1 (unip x * infGL E a (d * c)) = ψ.1 (infGL E a (unip z * (d * c))) := by
    rw [hx, mul_assoc, mul_assoc, ← infGL_comm, ← mul_assoc (infGL E a (unip z)), ← map_mul, hψ.1.left]
    have := congrArg (fun φ : Sm E a => φ.1 (infGL E a (unip z * (d * c)))) hk'
    exact this
  rw [e]
  exact hvar ψ r d hr hrt hd M hM hY c hc z hz

end GlobalTheory
