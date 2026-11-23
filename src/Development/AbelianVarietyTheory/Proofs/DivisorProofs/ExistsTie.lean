module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem UDeep.exists_tie (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (_hpq : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf)
    (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) : ∃ w₂ : UWit D.X, D.Comparison₂ w₁ w₂ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hpt⟩ := D.same
  have e : spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) := by
    rw [← Spec.map_comp]; rfl
  have w : a ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [Category.assoc, e]; exact ha.1.w
  have e₁ := w₁.hα.1.lift_fst _ _ w
  let m : P₀.A.left ⟶ w₁.G.left := w₁.hα.1.lift _ _ w
  have hm : IsGrpPullback P₀.A w₁.G (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m :=
    w₁.hα.cancel (ha.congr e.symm e₁.symm) (w₁.hα.1.lift_snd _ _ w)
  have hβ : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (m ≫ w₁.β) :=
    (hm.comp w₁.hβ).congr (by rw [D.pt]; simp only [USetup.uΩ, Category.assoc]) rfl
  have hLβ : LBIso (D.X.ρ.P.L.pull a') (Xo.univ.t.PP.L.pull (m ≫ w₁.β)) :=
    LBIso.trans (pull_isLB D.X.ρ.P.isLB _) P₀.isLB (pull_isLB Xo.univ.t.PP.isLB _) hL'.symm
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL
        (GenSpread.lbIso_pull_comp m e₁.symm rfl w₁.hL))
  refine ⟨{ G := P₀.A, α := a', β := m ≫ w₁.β, hα := ha', hβ := hβ, hL := hLβ }, m, hm, rfl, fun x => ?_⟩
  obtain ⟨v, hv, hv'⟩ := hpt x
  refine ⟨v, ?_, hv'⟩
  show v ≫ m ≫ w₁.α = _
  rw [e₁, hv, ← Category.assoc, e]

end GlobalTheory.UPoinc
