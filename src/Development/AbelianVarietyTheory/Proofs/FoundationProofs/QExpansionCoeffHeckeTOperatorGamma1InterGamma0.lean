module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGamStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicitStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicitStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem coef_heckeT : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ),
    GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) +
      (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  intro N l q k σ hN hq _ hσ f n
  have hq0 : 0 < q := hq.pos
  obtain ⟨g, hg⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k (q : ℤ) σ hN hσ f
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f
  have hgs := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g
  have hU := GlobalTheory.T.hasSum_heckeUOperatorExplicit q (⇑f) (fun m => GlobalTheory.Hk.coef ⇑f m) hq0 hf
  have hV := GlobalTheory.T.hasSum_heckeVOperatorExplicit q (⇑g) (fun m => GlobalTheory.Hk.coef ⇑g m) hq0 hgs
  have hsum : ∀ τ : ℍ, HasSum (fun m => (GlobalTheory.Hk.coef ⇑f (q * m) +
      (q : ℂ) ^ (k - 1) * (if q ∣ m then GlobalTheory.Hk.coef ⇑g (m / q) else 0)) •
        Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.heckeT k q σ ⇑f τ) := by
    intro τ
    have h2 := (hU τ).add ((hV τ).mul_left ((q : ℂ) ^ (k - 1)))
    have e : GlobalTheory.Hk.heckeT k q σ ⇑f τ =
        GlobalTheory.Hk.uOp q ⇑f τ + (q : ℂ) ^ (k - 1) * GlobalTheory.Hk.vOp q ⇑g τ := by
      rw [hg]; rfl
    rw [e]
    convert h2 using 1 <;> ext m <;> simp only [smul_eq_mul] <;> ring
  rw [GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum _ _ hsum n, ← hg]

end GlobalTheory.Hk
