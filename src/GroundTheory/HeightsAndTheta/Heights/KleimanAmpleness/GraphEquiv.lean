module

import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDoubleStair
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KerAltSucc
public import Mathlib.Algebra.Module.Prod
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

namespace Staircase

structure DblData (R : Type) [CommRing R] where
  D : ℕ → ℕ → Type
  [gD : ∀ p q, AddCommGroup (D p q)]
  [mD : ∀ p q, Module R (D p q)]
  v : ∀ p q, D p q →ₗ[R] D (p + 1) q
  h : ∀ p q, D p q →ₗ[R] D p (q + 1)
  comm : ∀ p q, (v p (q + 1)).comp (h p q) = (h (p + 1) q).comp (v p q)
  A : ℕ → Type
  [gA : ∀ p, AddCommGroup (A p)]
  [mA : ∀ p, Module R (A p)]
  dA : ∀ p, A p →ₗ[R] A (p + 1)
  a : ∀ p, A p →ₗ[R] D p 0
  C : ℕ → Type
  [gC : ∀ q, AddCommGroup (C q)]
  [mC : ∀ q, Module R (C q)]
  dC : ∀ q, C q →ₗ[R] C (q + 1)
  c : ∀ q, C q →ₗ[R] D 0 q

attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC

variable {R : Type} [CommRing R]

structure DblData.Good (X : DblData R) : Prop where
  ha : ∀ p, (X.a (p + 1)).comp (X.dA p) = (X.v p 0).comp (X.a p)
  hc : ∀ q, (X.c (q + 1)).comp (X.dC q) = (X.h 0 q).comp (X.c q)
  ka : ∀ p, LinearMap.ker (X.a p) = ⊥
  ra : ∀ p, LinearMap.ker (X.h p 0) = LinearMap.range (X.a p)
  rh : ∀ p q, LinearMap.ker (X.h p (q + 1)) = LinearMap.range (X.h p q)
  kc : ∀ q, LinearMap.ker (X.c q) = ⊥
  rc : ∀ q, LinearMap.ker (X.v 0 q) = LinearMap.range (X.c q)
  rv : ∀ p q, LinearMap.ker (X.v (p + 1) q) = LinearMap.range (X.v p q)

open GroundTheory.Heights₂.Heights.Kleiman.CechDouble

private abbrev DblData.toStair (X : DblData R) : Stair.DblData R where
  D := X.D
  v := X.v
  h := X.h
  comm := X.comm
  A := X.A
  dA := X.dA
  a := X.a
  C := X.C
  dC := X.dC
  c := X.c

private theorem DblData.Good.toStair {X : DblData R} (hX : X.Good) : X.toStair.Good :=
  ⟨hX.ha, hX.hc, hX.ka, hX.ra, hX.rh, hX.kc, hX.rc, hX.rv⟩

namespace DblData

theorem comm_apply (X : DblData R) (p q : ℕ) (z : X.D p q) :
    X.v p (q + 1) (X.h p q z) = X.h (p + 1) q (X.v p q z) :=
  LinearMap.congr_fun (X.comm p q) z

def shift (X : DblData R) : DblData R where
  D p q := X.D (p + 1) q
  v p q := X.v (p + 1) q
  h p q := X.h (p + 1) q
  comm p q := X.comm (p + 1) q
  A p := X.A (p + 1)
  dA p := X.dA (p + 1)
  a p := X.a (p + 1)
  C q := LinearMap.range (X.v 0 q)
  dC q := (X.h 1 q).restrict (fun x hx => by
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨X.h 0 q z, X.comm_apply 0 q z⟩)
  c q := (LinearMap.range (X.v 0 q)).subtype

def up (X : DblData R) (n : ℕ) : X.D 0 n →ₗ[R] X.shift.C n := (X.v 0 n).rangeRestrict

theorem up_surj (X : DblData R) (n : ℕ) (w : X.shift.C n) : ∃ z, X.up n z = w := by
  have hw : (w : LinearMap.range (X.v 0 n)).1 ∈ LinearMap.range (X.v 0 n) := (w : LinearMap.range (X.v 0 n)).2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  exact ⟨z, Subtype.ext hz⟩

namespace Good

theorem shift {X : DblData R} (hX : X.Good) : X.shift.Good :=
  { ha := fun p => hX.ha (p + 1)
    hc := fun _ => LinearMap.ext fun _ => rfl
    ka := fun p => hX.ka (p + 1)
    ra := fun p => hX.ra (p + 1)
    rh := fun p q => hX.rh (p + 1) q
    kc := fun _ => Submodule.ker_subtype _
    rc := fun q => by
      show LinearMap.ker (X.v 1 q) = LinearMap.range (LinearMap.range (X.v 0 q)).subtype
      rw [Submodule.range_subtype]
      exact hX.rv 0 q
    rv := fun p q => hX.rv (p + 1) q }

theorem a_d {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) :
    X.a (p + 1) (X.dA p x) = X.v p 0 (X.a p x) :=
  LinearMap.congr_fun (hX.ha p) x

theorem c_d {X : DblData R} (hX : X.Good) (q : ℕ) (y : X.C q) :
    X.c (q + 1) (X.dC q y) = X.h 0 q (X.c q y) :=
  LinearMap.congr_fun (hX.hc q) y

theorem a_injective {X : DblData R} (hX : X.Good) (p : ℕ) : Function.Injective (X.a p) :=
  LinearMap.ker_eq_bot.mp (hX.ka p)

theorem c_injective {X : DblData R} (hX : X.Good) (q : ℕ) : Function.Injective (X.c q) :=
  LinearMap.ker_eq_bot.mp (hX.kc q)

theorem ex_a {X : DblData R} (hX : X.Good) (p : ℕ) {z : X.D p 0} (hz : X.h p 0 z = 0) :
    ∃ x, X.a p x = z := by
  have hm : z ∈ LinearMap.ker (X.h p 0) := LinearMap.mem_ker.mpr hz
  rw [hX.ra p] at hm
  exact LinearMap.mem_range.mp hm

theorem ex_h {X : DblData R} (hX : X.Good) (p q : ℕ) {z : X.D p (q + 1)} (hz : X.h p (q + 1) z = 0) :
    ∃ w, X.h p q w = z := by
  have hm : z ∈ LinearMap.ker (X.h p (q + 1)) := LinearMap.mem_ker.mpr hz
  rw [hX.rh p q] at hm
  exact LinearMap.mem_range.mp hm

theorem ex_c {X : DblData R} (hX : X.Good) (q : ℕ) {z : X.D 0 q} (hz : X.v 0 q z = 0) :
    ∃ y, X.c q y = z := by
  have hm : z ∈ LinearMap.ker (X.v 0 q) := LinearMap.mem_ker.mpr hz
  rw [hX.rc q] at hm
  exact LinearMap.mem_range.mp hm

theorem hh {X : DblData R} (hX : X.Good) (p q : ℕ) (z : X.D p q) : X.h p (q + 1) (X.h p q z) = 0 := by
  have hm : X.h p q z ∈ LinearMap.ker (X.h p (q + 1)) := by
    rw [hX.rh p q]; exact LinearMap.mem_range_self _ z
  exact LinearMap.mem_ker.mp hm

theorem ha0 {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) : X.h p 0 (X.a p x) = 0 := by
  have hm : X.a p x ∈ LinearMap.ker (X.h p 0) := by
    rw [hX.ra p]; exact LinearMap.mem_range_self _ x
  exact LinearMap.mem_ker.mp hm

theorem vc0 {X : DblData R} (hX : X.Good) (q : ℕ) (y : X.C q) : X.v 0 q (X.c q y) = 0 := by
  have hm : X.c q y ∈ LinearMap.ker (X.v 0 q) := by
    rw [hX.rc q]; exact LinearMap.mem_range_self _ y
  exact LinearMap.mem_ker.mp hm

end Good

def Rel : (n : ℕ) → (X : DblData R) → X.A n → X.C n → Prop
  | 0, X => fun x y => X.a 0 x = X.c 0 y
  | n + 1, X => fun x y => ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z)

theorem rel_zero {X : DblData R} {x : X.A 0} {y : X.C 0} : Rel 0 X x y ↔ X.a 0 x = X.c 0 y := Iff.rfl

theorem rel_succ {n : ℕ} {X : DblData R} {x : X.A (n + 1)} {y : X.C (n + 1)} :
    Rel (n + 1) X x y ↔ ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z) :=
  Iff.rfl

private theorem stair_rel (n : ℕ) (X : DblData R) (x : X.A n) (y : X.C n) :
    Stair.DblData.Rel n X.toStair x y ↔ Rel n X x y := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [Stair.DblData.rel_succ, rel_succ]
    exact exists_congr fun z => and_congr_right fun _ => ih X.shift x (X.up n z)

theorem Rel.zero : ∀ (n : ℕ) (X : DblData R), Rel n X 0 0
  | 0, X => rel_zero.mpr (by rw [map_zero, map_zero])
  | n + 1, X => rel_succ.mpr ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; exact Rel.zero n X.shift⟩

theorem Rel.add : ∀ (n : ℕ) (X : DblData R) {x₁ x₂ : X.A n} {y₁ y₂ : X.C n},
    Rel n X x₁ y₁ → Rel n X x₂ y₂ → Rel n X (x₁ + x₂) (y₁ + y₂) := by
  intro n
  induction n with
  | zero =>
    intro X x₁ x₂ y₁ y₂ h₁ h₂
    exact rel_zero.mpr (by rw [map_add, map_add, rel_zero.mp h₁, rel_zero.mp h₂])
  | succ n ih =>
    intro X x₁ x₂ y₁ y₂ h₁ h₂
    obtain ⟨z₁, e₁, r₁⟩ := rel_succ.mp h₁
    obtain ⟨z₂, e₂, r₂⟩ := rel_succ.mp h₂
    refine rel_succ.mpr ⟨z₁ + z₂, by rw [map_add, map_add, e₁, e₂], ?_⟩
    rw [map_add]
    exact ih X.shift r₁ r₂

theorem Rel.smul : ∀ (n : ℕ) (X : DblData R) (r : R) {x : X.A n} {y : X.C n},
    Rel n X x y → Rel n X (r • x) (r • y) := by
  intro n
  induction n with
  | zero =>
    intro X r x y h₁
    exact rel_zero.mpr (by rw [map_smul, map_smul, rel_zero.mp h₁])
  | succ n ih =>
    intro X r x y h₁
    obtain ⟨z, e, r₁⟩ := rel_succ.mp h₁
    refine rel_succ.mpr ⟨r • z, by rw [map_smul, map_smul, e], ?_⟩
    rw [map_smul]
    exact ih X.shift r r₁

def relSub (n : ℕ) (X : DblData R) : Submodule R (X.A n × X.C n) where
  carrier := {p | Rel n X p.1 p.2}
  add_mem' h₁ h₂ := Rel.add n X h₁ h₂
  zero_mem' := Rel.zero n X
  smul_mem' r _ hp := Rel.smul n X r hp

theorem cocycle : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x y, Rel n X x y → X.dA n x = 0 ∧ X.dC n y = 0 := by
  intro n X hX x y hxy
  exact Stair.DblData.cocycle n X.toStair hX.toStair x y ((stair_rel n X x y).2 hxy)

theorem exA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, X.dA n x = 0 → ∃ y, Rel n X x y := by
  intro n X hX x hx
  obtain ⟨y, hy⟩ := Stair.DblData.exA n X.toStair hX.toStair x hx
  exact ⟨y, (stair_rel n X x y).1 hy⟩

theorem exC : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, X.dC n y = 0 → ∃ x, Rel n X x y := by
  intro n X hX y hy
  obtain ⟨x, hx⟩ := Stair.DblData.exC n X.toStair hX.toStair y hy
  exact ⟨x, (stair_rel n X x y).1 hx⟩

theorem bdA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x₀ : X.A n, Rel (n + 1) X (X.dA n x₀) 0 := by
  intro n X hX x₀
  exact (stair_rel (n + 1) X (X.dA n x₀) 0).1 (Stair.DblData.bdA n X.toStair hX.toStair x₀)

theorem bdC (n : ℕ) (X : DblData R) (hX : X.Good) (y₀ : X.C n) : Rel (n + 1) X 0 (X.dC n y₀) := by
  exact (stair_rel (n + 1) X 0 (X.dC n y₀)).1 (Stair.DblData.bdC n X.toStair hX.toStair y₀)

theorem kerC : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, Rel n X 0 y → y ∈ bdry X.dC n := by
  intro n X hX y hy
  exact Stair.DblData.kerC n X.toStair hX.toStair y ((stair_rel n X 0 y).2 hy)

theorem kerA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, Rel n X x 0 → x ∈ bdry X.dA n := by
  intro n X hX x hx
  exact Stair.DblData.kerA n X.toStair hX.toStair x ((stair_rel n X x 0).2 hx)

end DblData

theorem graph_equiv {M N M' N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (dM : M →ₗ[R] M') (dN : N →ₗ[R] N') (BM : Submodule R M) (BN : Submodule R N)
    (G : Submodule R (M × N))
    (hZ : ∀ x y, (x, y) ∈ G → dM x = 0 ∧ dN y = 0)
    (hM : ∀ x, dM x = 0 → ∃ y, (x, y) ∈ G)
    (hN : ∀ y, dN y = 0 → ∃ x, (x, y) ∈ G)
    (hBM : ∀ x ∈ BM, (x, (0 : N)) ∈ G) (hBN : ∀ y ∈ BN, ((0 : M), y) ∈ G)
    (hKM : ∀ x, (x, (0 : N)) ∈ G → x ∈ BM) (hKN : ∀ y, ((0 : M), y) ∈ G → y ∈ BN) :
    Nonempty ((LinearMap.ker dM ⧸ BM.comap (LinearMap.ker dM).subtype) ≃ₗ[R]
      (LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype)) := by
  exact Stair.graph_equiv dM dN BM BN G hZ hM hN hBM hBN hKM hKN

namespace DblData

theorem bdryA (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (x : X.A n), x ∈ bdry X.dA n → Rel n X x 0 := by
  intro n
  cases n with
  | zero =>
    intro x hx
    have hx0 : x = 0 := (Submodule.mem_bot R).mp hx
    subst hx0
    exact Rel.zero 0 X
  | succ n =>
    intro x hx
    obtain ⟨x₀, rfl⟩ := (LinearMap.mem_range (f := X.dA n)).mp hx
    exact bdA n X hX x₀

theorem bdryC (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (y : X.C n), y ∈ bdry X.dC n → Rel n X 0 y := by
  intro n
  cases n with
  | zero =>
    intro y hy
    have hy0 : y = 0 := (Submodule.mem_bot R).mp hy
    subst hy0
    exact Rel.zero 0 X
  | succ n =>
    intro y hy
    obtain ⟨y₀, rfl⟩ := (LinearMap.mem_range (f := X.dC n)).mp hy
    exact bdC n X hX y₀

theorem equiv (X : DblData R) (hX : X.Good) (n : ℕ) : Nonempty (H X.dA n ≃ₗ[R] H X.dC n) :=
  graph_equiv (X.dA n) (X.dC n) (bdry X.dA n) (bdry X.dC n) (relSub n X)
    (fun x y hr => cocycle n X hX x y hr) (fun x hx => exA n X hX x hx) (fun y hy => exC n X hX y hy)
    (fun x hx => bdryA X hX n x hx) (fun y hy => bdryC X hX n y hy)
    (fun x hr => kerA n X hX x hr) (fun y hr => kerC n X hX y hr)

end DblData

end Staircase

theorem Staircase.proof : Staircase.Statement := by
  intro R _ D _ _ v h A _ _ dA a C _ _ dC c hvh ha hc ka ra rh kc rc rv n
  exact Staircase.DblData.equiv
    { D := D, v := v, h := h, comm := hvh, A := A, dA := dA, a := a, C := C, dC := dC, c := c }
    ⟨ha, hc, ka, ra, rh, kc, rc, rv⟩ n

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
