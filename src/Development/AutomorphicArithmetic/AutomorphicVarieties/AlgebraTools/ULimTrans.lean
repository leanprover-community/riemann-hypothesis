module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimKer
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

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.trans_ker :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a b : Ideal R), a.FG → Antitone I → ∀ h : b ≤ a,
      Function.Surjective (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) ∧
      LinearMap.ker (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) = a • ⊤ ∧
      (a • ⊤ : Submodule R (ULim F (fun j => a ⊔ I j) M)) = ⊥ := by
  intro R _ F hF I M _ _ a b ha hI h
  have hI1 : Antitone fun j => b ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) b
  have hI2 : Antitone fun j => a ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) a
  have e1 : ∀ j, a ⊔ (b ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_eq_left.mpr h]
  have e2 : ∀ j, a ⊔ (a ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_idem]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M y
    exact ⟨ULim.mk F (fun j => b ⊔ I j) M p, by rw [ULim.map_mk]; rfl⟩
  · ext x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => b ⊔ I j) M x
    rw [LinearMap.mem_ker, ULim.map_mk, ULim.mk_eq_zero, ULim.mem_smul_top_iff R F hF _ M a ha hI1]
    simp only [LinearMap.id_apply, e1]
  · refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M x
    rw [ULim.mem_smul_top_iff R F hF _ M a ha hI2] at hx
    rw [Submodule.mem_bot, ULim.mk_eq_zero]
    simpa only [e2] using hx
