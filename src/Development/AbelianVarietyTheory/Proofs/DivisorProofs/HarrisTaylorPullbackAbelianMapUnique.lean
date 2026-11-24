module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MapUniq

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_auto {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f : S' ⟶ S} (m m' : ObjMap o' o f) : ∃ a : ObjMap o' o' (𝟙 S'), a.φ ≫ m'.φ = m.φ := by
  have w : m.φ ≫ o.A.hom = o'.A.hom ≫ f := m.cart.1.w
  set ψ := m'.cart.1.lift m.φ o'.A.hom w
  have hψ : ψ ≫ m'.φ = m.φ := m'.cart.1.lift_fst _ _ _
  have hψ₀ : ψ ≫ o'.A.hom = o'.A.hom := m'.cart.1.lift_snd _ _ _
  have hψ' : ψ ≫ o'.A.hom = o'.A.hom ≫ 𝟙 S' := by rw [Category.comp_id]; exact hψ₀
  have n : IsGrpPullback o'.A o.A (𝟙 S' ≫ f) (ψ ≫ m'.φ) := by rw [hψ, Category.id_comp]; exact m.cart
  obtain ⟨ψ₂, sq⟩ := exists_isSquare hψ'
  have e : m.φ₂ = ψ₂ ≫ m'.φ₂ := isSquare_unique m.sq (hψ ▸ isSquare_comp sq m'.sq)
  have hact : ∀ c, (o'.act.act c).left ≫ ψ = ψ ≫ (o'.act.act c).left := by
    intro c
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.act, Category.assoc, m'.act, ← Category.assoc, hψ]
    · rw [Category.assoc, hψ₀, Over.w, Category.assoc, Over.w, hψ₀]
  have heta : ∀ y, (o'.eta y).left ≫ ψ = 𝟙 S' ≫ (o'.eta y).left := by
    intro y
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.eta, Category.id_comp, m'.eta]
    · rw [Category.assoc, hψ₀, Category.id_comp]
  exact ⟨{ φ := ψ
           φ₂ := ψ₂
           cart := m'.cart.cancel n hψ'
           sq := sq
           act := hact
           pol := LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB o'.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m'.pol ψ₂ e))
           eta := heta }, hψ⟩

theorem objMap_φ_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s')
    (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  intro p _ D R _ b N hN hNp S S' s s' o' o f m m'
  obtain ⟨a, ha⟩ := exists_auto m m'
  have h1 := GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp S' s' o' a
  rw [← ha, h1, Category.id_comp]

end GlobalTheory.UPel.HT.MapUniq
