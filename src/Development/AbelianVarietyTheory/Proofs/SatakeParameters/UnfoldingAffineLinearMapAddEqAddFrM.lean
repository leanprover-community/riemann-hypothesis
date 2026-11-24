module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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

namespace GlobalTheory.PadicUnfold

open Formalism.L2.Col

variable {g : ℕ} [Fact g.Prime]

theorem eN_eq {k : Type} [CommRing k] {N : ℕ} (s : Fin N) : Loc.eN k N s.1 = Pi.single s 1 := by
  funext l
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem atN_eq {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (l : Fin N) : Loc.atN v l.1 = v l := by
  simp [Loc.atN]

section Affine

variable {k : Type} [CommRing k] {n' c' n c : ℕ}

theorem linearMap_unfolding_apply_single (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : Loc.FC n' c' n c → k)
    (s : Fin (n' + c')) (l : Fin (n + c)) :
    Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then
        (if hl : l.1 < n then xj (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  simp [Loc.xx1, Matrix.toLin'_apply, LinearMap.toMatrix'_apply]

theorem hom_ext {a b : ℕ} {x y : (Fin a → k) →ₗ[k] (Fin b → k)}
    (h : ∀ s l, x (Pi.single s 1) l = y (Pi.single s 1) l) : x = y := by
  refine LinearMap.pi_ext' fun s => LinearMap.ext_ring ?_
  funext l
  simpa using h s l

theorem chArg_add (x y : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) :
    Loc.chArg (x + y) = Loc.chArg x + Loc.chArg y := by
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Loc.atN
  split_ifs <;> simp

theorem chArg_eq (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) :
    Loc.chArg x = ∑ i : Fin c,
      x (Pi.single ⟨n' + i.1 + 1, by omega⟩ 1) ⟨n + i.1, by omega⟩ := by
  unfold Loc.chArg
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← eN_eq]
  exact atN_eq _ ⟨n + i.1, by omega⟩

end Affine

end GlobalTheory.PadicUnfold
