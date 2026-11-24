module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Lat

def TConj {ι Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) (t : Kˣ × Kˣ) (P P' : PD ι Γ R) : Prop :=
  (∀ g, (P'.r g).map f = tconj t ((P.r g).map f)) ∧ ∀ v, (P'.n v).map f = tconj t ((P.n v).map f)

def nCo {R : Type} [CommRing R] (X : M4 R) (w : ℤ × ℤ) : R :=
  if w = -wAl then X 1 0 else if w = -wBe then X 2 1 else if w = -wPs then X 2 0 else if w = -wTh then X 3 0 else 0

def Tight {ι Γ R : Type} [Group Γ] [CommRing R] (P : PD ι Γ R) : Set (ℤ × ℤ) :=
  {w | w ∈ roots ∧ (Ent P.r w ∨ ∃ v, nCo (P.n v) w ≠ 0)}

def CompanionTheory (Si : Set (ℤ × ℤ)) : Prop :=
  (wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP) ∨ (-wAl ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ qQ) ∨ (-wTh ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ {-wTh, -wPs}) ∨
    (-wAl ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ nM) ∨ (-wTh ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe}) ∨
    (-wTh ∈ Si ∧ wAl ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe, wAl})

variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)

structure PreRes [TopologicalSpace Γ] (P : PD Φ.ι Γ R) : Prop where
  pair : Φ.IsPair a P
  diag : ∀ g i, P.r g i i = a (Φ.χ i g)
  char : ∀ v, ∀ s ∈ Φ.Gv v, ∀ i, P.ψ v i s = a (Φ.χ i s)
  cont : P.Cont ⊥

def OddVan [TopologicalSpace Γ] : Prop :=
  ∀ w ∈ oddRoots, ∀ z ∈ Φ.Zgl a w, ∀ m : Φ.ι → R, Φ.LocTriv a w z m → z = 0 ∧ m = 0

def EntVan (P : PD Φ.ι Γ R) : Prop :=
  ∀ i j, wt i j ∈ oddRoots → (∀ g h x, x ≠ i → x ≠ j → P.r g i x * P.r h x j = 0) → ∀ m : Φ.ι → R,
    (∀ v, ∀ s ∈ Φ.Gv v, P.r s i j = m v * (a (Φ.χ j s) - a (Φ.χ i s))) → (∀ g, P.r g i j = 0) ∧ m = 0

end UpperTheory.V.Ws.Lat

end
