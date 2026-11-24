module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

def IsQuasiInv {Y : Scheme.{0}} {A B : Over Y} [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 A) ^ k ∧ ψ' ≫ ψ = (𝟙 B) ^ k

def IsAxesTriv {Y : Scheme.{0}} (B : Over Y) [GrpObj B] [IsCommMonObj B] (Q : LB (G2 B).left) : Prop :=
  Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) ∧
    ∃ t : (Q.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Y : Scheme.{0}}
  {s : Y ⟶ Sp R}

theorem isAxesTriv_obj (o : Obj b N s) : IsAxesTriv o.A o.P := ⟨o.isLB, o.rig₁, o.rig₂⟩

def KerStableAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A, g ≫ ψ = 1 →
    ∀ a : D.O, g ≫ o.act.act a ≫ ψ = 1

def PullPolTriv (o : Obj b N s) {B : Over Y} (ψ' : B ⟶ o.A) {T : Over Y} (x : T ⟶ B) : Prop :=
  ∃ τ : (o.P.pull (lift (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ')).left).Gen, τ.IsGen

def PolKerAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ' : B ⟶ o.A) (c : ℕ) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ x : T ⟶ B, x ^ (c ^ 3) = 1 →
    (PullPolTriv o ψ' x ↔ x ^ c = 1)

def TjAt (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Y), (∃ σ : Sp k ⟶ Tb, σ ≫ t = x) →
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

theorem tjAt_id_iff (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) :
    TjAt r w j o ψ (𝟙 Y) ↔ IsTj r w j o o' ψ :=
  ⟨fun h k _ _ _ x => h k x ⟨x, Category.comp_id x⟩, fun h k _ _ _ x _ => h k x⟩

theorem IsPIsog.kerStableAt {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : KerStableAt o ψ t := by
  intro T _ _ g hg a
  haveI := o'.act.hom a
  rw [h.2.2.1, ← Category.assoc, hg, one_comp]

theorem IsPIsog.exists_quasiInv {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ) :
    ∃ ψ' : o'.A ⟶ o.A, IsQuasiInv c ψ ψ' := by
  obtain ⟨-, h1, -, -, -, ψ', h2, h3, h4⟩ := h
  exact ⟨ψ', h1, h2, h3, h4⟩

end GlobalTheory.UPel.HT.ES
