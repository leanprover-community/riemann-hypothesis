module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
public import Mathlib.Algebra.DualNumber
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

abbrev fstD (R : Type) [CommRing R] : DualNumber R →ₐ[R] R := TrivSqZeroExt.fstHom R R R

theorem kerD_sq : (RingHom.ker (fstD R)) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  have ha0 : a.fst = 0 := ha
  have hb0 : b.fst = 0 := hb
  rw [Ideal.mem_bot, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha0 rfl,
    show b = TrivSqZeroExt.inr b.snd from TrivSqZeroExt.ext hb0 rfl, TrivSqZeroExt.inr_mul_inr]

theorem inr_mem_kerD (t : R) : (TrivSqZeroExt.inr t : DualNumber R) ∈ RingHom.ker (fstD R) :=
  TrivSqZeroExt.fst_inr R t

def dualLift {n : ℕ} (c : Fin n → R) : JetR R (Fin n) 1 →ₐ[R] DualNumber R :=
  jetLift (R := R) (RingHom.ker (fstD R)) kerD_sq (fun j => TrivSqZeroExt.inr (c j))
    (fun j => inr_mem_kerD (c j))

theorem dualLift_zR {n : ℕ} (c : Fin n → R) (j : Fin n) : dualLift c (zR 1 j) = TrivSqZeroExt.inr (c j) :=
  jetLift_zR _ _ _ _ j

theorem fstD_comp_dualLift {n : ℕ} (c : Fin n → R) : (fstD R).comp (dualLift c) = jetAug R (Fin n) 1 :=
  jet_ext fun j => by rw [AlgHom.comp_apply, dualLift_zR, jetAug_zR]; exact inr_mem_kerD (c j)

theorem eq_dualLift {n : ℕ} (ψ : JetR R (Fin n) 1 →ₐ[R] DualNumber R) (h : (fstD R).comp ψ = jetAug R (Fin n) 1) :
    ψ = dualLift (fun j => (ψ (zR 1 j)).snd) :=
  jet_ext fun j => by
    rw [dualLift_zR]
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_inr]
      have := AlgHom.congr_fun h (zR 1 j)
      rw [AlgHom.comp_apply, jetAug_zR] at this
      exact this
    · rfl

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem comp_one' {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem spMap_jetAug_alt {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (m : ℕ) : spMap (jetAug R (Fin n) m) ≫ x m = 1 := by
  have e : jetAug R (Fin n) m = (jetAug R (Fin n) 0).comp (jetZeroR R (Fin n) m) :=
    (jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm)
  rw [e, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']

def IsTan (w : sp (R₀ := R) (DualNumber R) ⟶ G) : Prop := spMap (fstD R) ≫ w = 1

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

include hx in
theorem isTan_dualLift (c : Fin n → R) : IsTan (spMap (dualLift c) ≫ x 1) := by
  rw [IsTan, ← Category.assoc, spMap_comp, fstD_comp_dualLift]
  exact spMap_jetAug_alt hx 1

include hx in
theorem exists_coord (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) :
    ∃! c : Fin n → R, w = spMap (dualLift c) ≫ x 1 := by
  obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := hx.2.2 (DualNumber R) (fstD R) 1 kerD_sq w hw
  refine ⟨fun j => (ψ (zR 1 j)).snd, ?_, ?_⟩
  · show w = spMap (dualLift (fun j => (ψ (zR 1 j)).snd)) ≫ x 1
    rw [← eq_dualLift ψ h1]
    exact h2
  · intro c hc
    have := hu (dualLift c) ⟨fstD_comp_dualLift c, hc⟩
    rw [← this]
    funext j
    rw [dualLift_zR, TrivSqZeroExt.snd_inr]

def tcoord (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) : Fin n → R :=
  (exists_coord hx w hw).exists.choose

theorem tcoord_spec (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) :
    w = spMap (dualLift (tcoord hx w hw)) ≫ x 1 :=
  (exists_coord hx w hw).exists.choose_spec

theorem tcoord_eq (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) (c : Fin n → R)
    (hc : w = spMap (dualLift c) ≫ x 1) : tcoord hx w hw = c :=
  (exists_coord hx w hw).unique (tcoord_spec hx w hw) hc

end ReciprocityTheory.ChartRestriction.G.Chart
