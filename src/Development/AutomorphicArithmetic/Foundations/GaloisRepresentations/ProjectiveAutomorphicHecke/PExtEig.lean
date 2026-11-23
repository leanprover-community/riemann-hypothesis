module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
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

open Module

universe u v

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp [rop, Finsupp.sum, Finset.sum_add_distrib, smul_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Finsupp.sum, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => smul_comm _ _ _

private def eigForms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (r : J → H →₀ ℂ) (θ : J → ℂ) :
    Submodule ℂ (H → V) where
  carrier := {Φ | Φ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Φ = θ j • Φ}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun j => by rw [rop_add, ha', hb', smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun j => by
    have := rop_smul (r j) (0 : ℂ) (0 : H → V)
    simpa using this⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨Submodule.smul_mem _ a hb, fun j => by rw [rop_smul, hb', smul_comm]⟩

end

end UpperTheory.Gal.CertificateRingHomMap

end
