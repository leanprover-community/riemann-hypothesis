module

public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockCombStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.LocalRingCardinality.DataCoeff
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AntitoneOfMemInterl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

def kChar {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : ℂ :=
  LinearMap.trace ℂ T.V ((T.op k : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V)

def SqCharStatement : Prop :=
  ∀ (N : ℕ) (lam : Formalism.BasicNotions.DomWeight N) (g : GL (Fin N) ℂ) (t : Fin N → ℂ),
    (g : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal t →
    ∃ f : Formalism.BasicNotions.nablaSq ℂ N lam →ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam,
      (∀ x, (f x : MvPolynomial (Fin N × Fin N) ℂ) = Formalism.BasicNotions.sqAct ℂ N lam g x) ∧
      LinearMap.trace ℂ _ f = gtChar N lam.w t

def UCharStatement : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℤ), Antitone Λ →
    ∀ (T : KType (fun _ : Fin N => true) (fun a => (Λ a : ℝ))) (k : KG (fun _ : Fin N => true)) (t : Fin N → ℂ),
      toMK k = Matrix.diagonal t → kChar T k = gtChar N Λ t

def KCharGTStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℤ), (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) →
    ∀ (T : KType ε (fun a => (Λ a : ℝ))) (k : KG ε) (t : Fin n → ℂ), toMK k = Matrix.diagonal t →
      kChar T k = gtChar (cnt ε true) (Λ ∘ blk ε true) (t ∘ blk ε true) *
        gtChar (cnt ε false) (Λ ∘ blk ε false) (t ∘ blk ε false)

def WeylStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℤ), (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) →
    ∀ (T : KType ε (fun a => (Λ a : ℝ))) (k : KG ε) (t : Fin n → ℂ), toMK k = Matrix.diagonal t →
      wdenK ε t * kChar T k = numK ε (Λ + rhoK ε) t

theorem ne_zero_of_toMK_diag {n : ℕ} {ε : Fin n → Bool} (k : KG ε) {t : Fin n → ℂ}
    (hk : toMK k = Matrix.diagonal t) (i : Fin n) : t i ≠ 0 := by
  unfold toMK toM at hk
  have hu : IsUnit (Matrix.diagonal t) := by
    rw [← hk]
    first
    | exact Units.isUnit _
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet.ne_zero i (Finset.mem_univ i)

theorem antitone_blk {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℤ}
    (hdom : ∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) (b : Bool) : Antitone (Λ ∘ blk ε b) := by
  have hmem : ∀ r, ε (blk ε b r) = b := by
    intro r
    have hr := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl r
    show ε ((univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl r) = b
    simpa using hr
  have hsm : StrictMono (blk ε b) :=
    (Finset.orderEmbOfFin (univ.filter fun i : Fin n => ε i = b) rfl).strictMono
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · exact hdom _ _ (hsm h) ((hmem i).trans (hmem j).symm)
  · rw [h]

theorem weyl_of (hK : KCharGTStatement) (hB : BlockCombStatement) : WeylStatement := by
  have hW : WeylGTStatement := weylGT
  intro n ε Λ hdom T k t hk
  rw [hK n ε Λ hdom T k t hk]
  obtain ⟨hw, hnum, hrho⟩ := hB ℂ n ε (Λ + rhoK ε) t
  rw [hw, hnum]
  have hG : ∀ b : Bool, wden (cnt ε b) (t ∘ blk ε b) * gtChar (cnt ε b) (Λ ∘ blk ε b) (t ∘ blk ε b) =
      alt (cnt ε b) ((Λ + rhoK ε) ∘ blk ε b) (t ∘ blk ε b) := by
    intro b
    have hc : (Λ + rhoK ε) ∘ blk ε b = Λ ∘ blk ε b + delta (cnt ε b) := by
      rw [← hrho b]
      rfl
    rw [hc]
    exact hW ℂ _ _ (antitone_blk hdom b) _ (fun i => ne_zero_of_toMK_diag k hk _)
  rw [← hG true, ← hG false]
  ring

end ReciprocityTheory.ChartRestriction.TR.Weyl
