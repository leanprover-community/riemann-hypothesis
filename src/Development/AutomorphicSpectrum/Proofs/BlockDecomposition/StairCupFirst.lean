module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairCupFirst

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}
  {T₁ : Res.{1} F₁} {T₂ : Res.{1} F₂} {T₃ : Res.{1} F₃} {P : Pairing F₁ F₂ F₃}

theorem term_dvC {F : C ⥤ ModuleCat.{0} R} {T : Res.{1} F} (hT : T.Good) {s p n : ℕ}
    (σ : ComposableArrows C n) (a : Cn (T.K s) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (s + 1)) σ (T.dvC s p a) g hg = T.dv s _ (term (T.K s) σ a g hg) := by
  delta CrystallineSemistableComparison.CH.term CrystallineSemistableComparison.E.Res.dvC
  exact (hT.dv_nat s _ _).symm

theorem dvC_cupC (μ : ResPair T₁ T₂ T₃ P) (h₁ : T₁.Good) (h₂ : T₂.Good) {s t r k : ℕ} (h : s + t = r)
    (a : Cn (T₁.K s) k) (y : Cn (T₂.K t) 0) (hy : T₂.dvC t 0 y = 0) :
    T₃.dvC r k ((μ.μ s t r h).cupC (add_zero k) a y) =
      (μ.μ (s + 1) t (r + 1) (by omega)).cupC (add_zero k) (T₁.dvC s k a) y := by
  delta CrystallineSemistableComparison.E.Res.dvC CrystallineSemistableComparison.CH.Pairing.cupC
  funext σ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mk₂_apply]
  have hz : ∀ (g : Fin (0 + 1) → Fin (k + 1)) (hg : Monotone g),
      CrystallineSemistableComparison.CH.term (T₂.K (t + 1)) σ (0 : Cn (T₂.K (t + 1)) 0) g hg = 0 := fun g hg => by
    delta CrystallineSemistableComparison.CH.term
    exact map_zero _
  rw [μ.leib, ← term_dvC h₂ σ y, hy, hz, map_zero, smul_zero, add_zero, ← term_dvC h₁ σ a]
  rfl

theorem stCupA : CrystallineSemistableComparison.E.CupLeib.{1} → CrystallineSemistableComparison.E.StCupA := by
  intro hL R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ h₁ h₂ i t n z y u hy hdy hst s
  induction s with
  | zero =>
    intro k r h x hx
    obtain ⟨hik, rfl⟩ := hx
    subst hik
    obtain rfl : r = t := by omega
    exact hst
  | succ s ih =>
    intro k r h x hx
    obtain ⟨a, rfl, hsa⟩ := hx
    obtain rfl : r = s + t + 1 := by omega
    show ∃ a', T₃.dvC (s + t) k a' = _ ∧
      T₃.St u (s + t) (k + 1) ((-1) ^ k • CrystallineSemistableComparison.CH.d (T₃.K (s + t)) k a')
    refine ⟨(μ.μ s t (s + t) rfl).cupC (add_zero k) a y, dvC_cupC μ h₁ h₂ rfl a y hy, ?_⟩
    have hcup := hL R C (T₁.K s) (T₂.K t) (T₃.K (s + t)) (μ.μ s t (s + t) rfl) k 0 k (add_zero k) a y
    rw [hcup, hdy, map_zero, smul_zero, add_zero, ← LinearMap.smul_apply, ← map_zsmul]
    exact ih (k + 1) (s + t) rfl _ hsa

end GlobalTheory.CompanionTheory.StairCupFirst
