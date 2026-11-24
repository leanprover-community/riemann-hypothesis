module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GlobWIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def Ap (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Subalgebra (𝓞 I.E) I.E where
  carrier := {x | ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E)}
  mul_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, a * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t * y) * ha + (a : I.E) * hb
  add_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t : I.E) * ha + (↑s : I.E) * hb
  algebraMap_mem' := by
    intro a
    exact ⟨1, Nat.coprime_one_left p, a, by simp⟩

def LA (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Submodule (Ap I p) (Fin I.n → I.E) :=
  Submodule.span (Ap I p) (I.L : Set (Fin I.n → I.E))

def ApPID : Prop := ∀ (I : Formalism.MainNotions.S.AutInst) (p : ℕ), p.Prime → IsPrincipalIdealRing (Ap I p)

def WFrame : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p r k : ℕ) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M p → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ w wd : Fin (k + 1) → Fin I.n → I.E,
      (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) ∧
      (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) ∧
      (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)

def PPAssemble : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E),
    p.Prime → 1 ≤ m → Hyp I (p ^ m) r k θ e f M →
    (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) →
    (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) →
    (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) →
    (∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)) →
    Concl I (p ^ m) r k θ e f M

theorem gwpp_of (h1 : WFrame) (h2 : PPAssemble) : GWpp := by
  intro I p m r k θ e f M hp hm hH
  obtain ⟨_, _, _, hn, hee, hff, hef, hM, hL⟩ := id hH
  have hMp : Nat.Coprime M p :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hM
  obtain ⟨w, wd, hw, horth, hdual, hspan⟩ := h1 I p r k e f M hp hn hee hff hef hMp hL
  exact h2 I p m r k θ e f M w wd hp hm hH hw horth hdual hspan

end PI.ScRefExists.Sk
