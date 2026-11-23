module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
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
import Mathlib.Tactic.Basify
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.GLift

theorem embHom_apply_cc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.castSucc j) = a i j := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc]

theorem embHom_apply_cl {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.last r) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_lc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.castSucc j) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_ll {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.last r) = 1 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_last]

theorem coe_emb {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    ((GlobalTheory.JR.Step.emb r F g : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F (g : Matrix (Fin r) (Fin r) F) := rfl

theorem coe_emb_inv {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    (((GlobalTheory.JR.Step.emb r F g)⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
  rw [← map_inv]; rfl

theorem emb_preimage_glO : ∀ (F : Type) [NormedField F] (r : ℕ),
    ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  intro F _ r
  ext g
  simp only [Set.mem_preimage, glO, Set.mem_setOf_eq, coe_emb, coe_emb_inv]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    rwa [embHom_apply_cc, embHom_apply_cc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [embHom_apply_ll]
    · simp [embHom_apply_lc]
    · simp [embHom_apply_cl]
    · rw [embHom_apply_cc, embHom_apply_cc]; exact h i j

end GlobalTheory.JR.GLift
