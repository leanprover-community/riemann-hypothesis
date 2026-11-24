module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin)
open scoped Matrix

theorem UpperTheory.exists_contragredient_cuspSub :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∃ π₂ : TR.CuspSub F a, (∃ S : π.V ≃ₗ[ℂ] π₂.V, (∀ k φ, π₂.op (.fin k) (S φ) = S (π.op (.fin (invT a (Af F) k)) φ)) ∧
          (∀ k φ, π₂.op (.cpt k) (S φ) = S (π.op (.cpt k) φ)) ∧
          ∀ X φ, π₂.op (.lie X) (S φ) = S (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) φ)) ∧
        (∀ v m, π.HasInfChar v m → π₂.HasInfChar v (m.map Neg.neg)) ∧ ∀ w B, π.HasSat w B → π₂.HasSat w (B.map (·⁻¹)) := by
  intro F _ _ _ a π
  exact ⟨π.dual, ⟨π.toDual, fun k φ => π.op_toDual (.fin k) φ, fun k φ => π.op_toDual (.cpt k) φ,
    fun X φ => π.op_toDual (.lie X) φ⟩, fun _ _ h => h.dual, fun _ _ h => h.dual⟩
