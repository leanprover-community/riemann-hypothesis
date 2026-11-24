module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittaker
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker : ∀ (D : D7) (Γ V : Type) [Group Γ] [Finite Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G0g D.nd) (ι : G0g D.nd →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup (G0g D.nd)), (∀ k, IsHalf D k (H k)) → ∀ (n : Fin 2 → ℕ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → ∀ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) → ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) : ℝ) ≤ c * (locShare D (fun k _ => eUk D k (ψ₀ k)) 0 (S 0) + locShare D (fun k _ => eUk D k (ψ₀ k)) 1 (S 1)) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  first | exact @GlobalTheory.BadCount.bad_part_le_locShare | exact GlobalTheory.BadCount.bad_part_le_locShare | (intros; apply GlobalTheory.BadCount.bad_part_le_locShare <;> assumption)
