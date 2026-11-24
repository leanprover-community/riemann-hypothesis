module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory NumberField Filter Topology

noncomputable section

namespace Formalism.MainNotions.S.LocalFrameAxioms

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def LocMatch (D : D7) (T T' : ℝ) (x : LocalDataRealPlace D) (B : LocBessel D.R.k D.R.rS) : Prop :=
  B.lam = x.lam ∧ B.u = x.u ∧ B.u' = x.u' ∧ Tz D.R.k D.R.rS B.z = T ∧ Tz D.R.k D.R.rS B.z' = T' ∧
    B.ε = epsSH D.R

def FrameAx (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) (B : D.what₂.Tau → LocBessel D.R.k D.R.rS) : Prop :=
  ∃ ϱ : ℝ, IsFrameScale D L ϱ ∧ ∀ v, (B v).c = cPsi D δ v / (ϱ : ℂ)

def PsiAx (D : D7) (δ : D.host.E) : Prop :=
  δ ≠ 0 ∧ ((∀ v, (plEmb D v δ).re = 0) ∨ ∀ v, (plEmb D v δ).im = 0)

theorem k_le_nS (D : D7) : D.R.k ≤ 2 * D.R.rS + D.R.k + 1 := by omega

def Nlet (D : D7) (Kst : ℕ) : ℝ := 4 * (Kst : ℝ) * ((D.R.rS : ℝ) + 1)

section Arith

open scoped ComplexOrder

variable (D : D7)

def InProd (Sg : ℕ → ℕ → Finset D.host.E) : ℕ → List (D.host.E × ℕ) → Prop
  | _, [] => True
  | a, (t, s) :: bs => t ∈ Sg (a + 1) s ∧ InProd Sg (a + s) bs

def headsOf (Sg : ℕ → ℕ → Finset D.host.E) (j : ℕ) : Set (Point D.host.E j) := {h | InProd D Sg 0 h.1}

def PSDKOn {α : Type*} (S : Set α) (K : α → α → ℂ) : Prop :=
  ∀ (X : Finset α) (a : α → ℂ), (∀ p ∈ X, p ∈ S) → 0 ≤ ∑ p ∈ X, ∑ q ∈ X, star (a p) * K p q * a q

def KLEOn {α : Type*} (S : Set α) (K L : α → α → ℂ) : Prop := PSDKOn S (fun p q => L p q - K p q)

def ArithAxF (L : LatticeDataWithDual D) (Kd : KernelData D) : Prop :=
  (∀ p q, Kd.K 0 p q = 1) ∧
  (∀ i, i ≤ D.R.rS + 1 → PSDK (Kd.K i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → 0 ≤ Kd.e i ∧ Kd.e i ≤ 1) ∧

  (∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 → ∀ (h h' : Point D.host.E j) (t t' : D.host.E)
      (ht : t ≠ 0) (ht' : t' ≠ 0),
      Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t' ht' s hs) ≠ 0 →
        (if j + s = D.R.rS + 1 ∧ s = 1 then t = t' else t⁻¹ - t'⁻¹ ∈ L.La' (j + 1) s)) ∧

  ∀ Sg : ℕ → ℕ → Finset D.host.E,
    ∃ Th : (j s : ℕ) → D.host.E → Point D.host.E j → Point D.host.E j → ℂ,
    ∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 →
      (∀ (t : D.host.E) (ht : t ≠ 0), t ∈ Sg (j + 1) s →
        KLEOn (headsOf D Sg j)
          (fun h h' : Point D.host.E j => Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t ht s hs)) (Th j s t)) ∧
      (∀ t, ∀ l ∈ L.La (j + 1) s, ∀ h ∈ headsOf D Sg j, ∀ h' ∈ headsOf D Sg j, Th j s (t + l) h h' = Th j s t h h') ∧
      (∀ t, PSDKOn (headsOf D Sg j) (Th j s t)) ∧
      (∀ X : Finset D.host.E, (∀ t ∈ X, ∀ t' ∈ X, t - t' ∈ L.La (j + 1) s → t = t') →
        KLEOn (headsOf D Sg j) (fun h h' => ∑ t ∈ X, Th j s t h h')
          (fun h h' => (1 + (Kd.e (j + s) : ℂ)) * Kd.K j h h'))

variable {D}

end Arith

end Formalism.MainNotions.S.LocalFrameAxioms

end
