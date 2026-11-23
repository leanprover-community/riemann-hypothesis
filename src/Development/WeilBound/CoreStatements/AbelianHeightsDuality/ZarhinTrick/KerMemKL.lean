module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamA
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamC
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem ker_memKL {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (l : A ⟶ B) [IsMonHom l] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) [IsCommMonObj ((Over.pullback s).obj A)]
    (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj A) (hx : x ≫ (Over.pullback s).map l = 1) :
    GlobalTheory.MemKL ((Over.pullback s).obj A) L x := by
  have hx0 : lam (cls L hL) (fst T ((Over.pullback s).obj A) ≫ x) (snd T ((Over.pullback s).obj A)) = 0 := by
    rw [lam_comm, lam_cL_pt s hD.isLB l L hL e, ← toBase_map, Category.assoc, hx, MonObj.comp_one, toBase_one]
    exact evc_one_right hD.isLB hD.zero _
  have hD' : (Out.translDiff ((Over.pullback s).obj A) L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T _) (snd T _)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = GlobalTheory.CechPic.pull (fst T ((Over.pullback s).obj A)).left
      (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T _).left ⁻¹ᵁ V).ι ≫ (fst T _).left) (fun z ↦ z.2) hc

end PositivityTheory.PrwZar.Z2
