module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraTraceMapOfCokernelKilledByScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemRangeOfSurjectiveLocalizedMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorMapInjectiveCokerKilledStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfMaximalIdealPowOfLocallySurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfTraceOfSmulMemRangeStatement
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  intro R _ _ _ _ A B _ _ _ _ _ _ hA hB ψ hψ ⟨s, hs, hsb⟩
  obtain ⟨k, hk⟩ := GlobalTheory.T.smul_mem_of_maximalIdeal_pow_of_locally_surjective R B (ψ.range.toSubmodule.restrictScalars R) (fun p hp hpm => by
    haveI := hp
    haveI := hA p hpm
    haveI := hB p hpm
    let S := Localization.AtPrime p
    haveI : Module.Free S (S ⊗[R] A) := Module.free_of_flat_of_isLocalRing
    haveI : Module.Free S (S ⊗[R] B) := Module.free_of_flat_of_isLocalRing
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.localization_tensor_map_injective_coker_killed R A B p ψ hψ s hs hsb
    have htr := GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar S _ _ _ h1 _ h2 h3
    exact GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map R A B p ψ (GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range S _ _ _ h1 _ h2 h3 htr))
  exact ⟨k, fun x hx b => hk x hx b⟩

end GlobalTheory.EtaleCoker
