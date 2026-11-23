module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIsoLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.PairAlg
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

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def pairSub {d d' : ℕ} (T : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d' → ℂ)) :
    Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ) where
  carrier := {p | ∀ v, T (p.1 *ᵥ v) = p.2 *ᵥ T v}
  mul_mem' := by
    intro p q hp hq v
    have hp' : ∀ v, T (p.1 *ᵥ v) = p.2 *ᵥ T v := hp
    have hq' : ∀ v, T (q.1 *ᵥ v) = q.2 *ᵥ T v := hq
    rw [Prod.fst_mul, Prod.snd_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp', hq']
  add_mem' := by
    intro p q hp hq v
    have hp' : ∀ v, T (p.1 *ᵥ v) = p.2 *ᵥ T v := hp
    have hq' : ∀ v, T (q.1 *ᵥ v) = q.2 *ᵥ T v := hq
    rw [Prod.fst_add, Prod.snd_add, Matrix.add_mulVec, Matrix.add_mulVec, map_add (f := _), hp', hq']
  algebraMap_mem' := by
    intro c v
    simp only [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd, Prod.fst_one, Prod.snd_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

theorem UpperTheory.V.AlgRepEndIrreducible.algIso :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a) (m : (E →+* ℂ) → Multiset ℂ),
      (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ τ (m τ)) → (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ' τ (m τ)) → ∃ T, IsAlgIso Ξ Ξ' T := by
  intro E _ _ _ a Ξ Ξ' m h h'
  obtain ⟨T, hT⟩ := algIsoLie E a Ξ Ξ' m h h'
  obtain ⟨h1, h2⟩ := pairAlg E a Ξ Ξ' (pairSub T) (fun τ i j v => hT τ i j v)
  exact ⟨T, fun y v => h2 y v, fun X v => h1 X v⟩
