module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundamentalDomainSmulIff
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

theorem fundamentalDomain_covol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K : Subgroup (HA (AF F) σ J), IsClosed (K : Set (HA (AF F) σ J)) → ∀ μ : Measure K, μ.IsHaarMeasure → (∃ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) ∧ (∀ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ → covol μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧ ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ ratOf (K := K), ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧ ∀ c : NNReal, c ≠ 0 → covol (c • μ) = (c : ℝ) * covol μ := by
  intro F E _ _ _ _ _ σ _ n J _ K _ μ hμ

  refine domains_and_covolume F E σ n J K (ratOf (K := K)) rfl covol ?_ μ hμ
  intro ν hν
  refine ⟨hν.choose, hν.choose_spec, ?_⟩
  rw [covol, dite_eq_left hν]

end GlobalTheory.ClosedSubgroupCovol
