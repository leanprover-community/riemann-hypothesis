module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.ModelFunctionsMultiply
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HcParamGapGeIndex
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

def CkModel : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : NonnegDom ε m) (k : KG ε),
    cK (modelKType ε hm) k = ‖f0K ε m k‖

def CkTwist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (c : ℤ),
    ∃ T' : KType ε (fun a => Λ a + (c : ℝ)), ∀ k, cK T' k = cK T k

def ModelFunctionsMultiply : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m₁ m₂ : Fin n → ℤ), NonnegDom ε m₁ → NonnegDom ε m₂ → ∀ k : KG ε,
    f0K ε (m₁ + m₂) k = f0K ε m₁ k * f0K ε m₂ k

theorem cK_transport {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T T' : KType ε Λ) (k : KG ε) : cK T k = cK T' k := by
  obtain ⟨φ, hφ, -, hw⟩ := kType_unique T T'
  unfold cK
  rw [← hw, ← hφ, LinearIsometryEquiv.inner_map_map]

theorem cK_eq_f0K (hM : CkModel) (hT : CkTwist) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (m : Fin n → ℤ) (hm : NonnegDom ε m) (c : ℤ) (hΛ : ∀ a, Λ a = (m a : ℝ) + c) (k : KG ε) :
    cK T k = ‖f0K ε m k‖ := by
  obtain ⟨T', hT'⟩ := hT n ε _ (modelKType ε hm) c
  have e : (fun a => ((m a : ℝ)) + (c : ℝ)) = Λ := funext fun a => (hΛ a).symm
  subst e
  rw [cK_transport T T' k, hT' k, hM n ε m hm k]

theorem exists_shift {ε : Fin n → Bool} {Λ : Fin n → ℝ} (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : ∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) :
    ∃ (m : Fin n → ℤ) (c : ℤ), NonnegDom ε m ∧ ∀ a, Λ a = (m a : ℝ) + c := by
  apply CompanionTheory.RgFd.exists_shift <;> assumption

theorem coefMul_dom (hM : CkModel) (hT : CkTwist) (hF : ModelFunctionsMultiply) {ε : Fin n → Bool} {Λ₁ Λ₂ : Fin n → ℝ}
    (h1 : (∀ a, ∃ m : ℤ, Λ₁ a = m) ∧ ∀ a b, a < b → ε a = ε b → Λ₁ b ≤ Λ₁ a)
    (h2 : (∀ a, ∃ m : ℤ, Λ₂ a = m) ∧ ∀ a b, a < b → ε a = ε b → Λ₂ b ≤ Λ₂ a)
    (T₁ : KType ε Λ₁) (T₂ : KType ε Λ₂) (T₃ : KType ε (Λ₁ + Λ₂)) (k : KG ε) :
    cK T₃ k = cK T₁ k * cK T₂ k := by
  obtain ⟨m₁, c₁, hm₁, e₁⟩ := exists_shift h1.1 h1.2
  obtain ⟨m₂, c₂, hm₂, e₂⟩ := exists_shift h2.1 h2.2
  have hm : NonnegDom ε (m₁ + m₂) :=
    ⟨fun a b hab he => by simp only [Pi.add_apply]; linarith [hm₁.1 a b hab he, hm₂.1 a b hab he],
      fun a => by simp only [Pi.add_apply]; linarith [hm₁.2 a, hm₂.2 a]⟩
  rw [cK_eq_f0K hM hT T₁ m₁ hm₁ c₁ e₁, cK_eq_f0K hM hT T₂ m₂ hm₂ c₂ e₂,
    cK_eq_f0K hM hT T₃ (m₁ + m₂) hm (c₁ + c₂) (fun a => by simp [e₁, e₂]; push_cast; ring),
    hF n ε m₁ m₂ hm₁ hm₂ k, norm_mul]

theorem dvec_int_dom (ε : Fin n → Bool) :
    (∀ a, ∃ m : ℤ, Dvec n a = m) ∧ ∀ a b, a < b → ε a = ε b → Dvec n b ≤ Dvec n a := by
  refine ⟨fun a => ⟨(n : ℤ) - 1 - (a : ℕ), by simp [Dvec]⟩, fun a b hab _ => ?_⟩
  simp only [Dvec]
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem coefPow_of (hM : CkModel) (hT : CkTwist) (hF : ModelFunctionsMultiply) : CoefPow := by
  apply CompanionTheory.RgFd.coefPow_of <;> assumption

end PositivityTheory.RgFd
