module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KerAxes

theorem triv_of_local_evc {S : Scheme.{0}} {G T : Over S} [GrpObj G] (hG : IsAbelianScheme G)
    {P : LB (G ⊗ G).left} (hP : P.IsLB) (h2 : Triv (ev P (𝟙 G) (1 : G ⟶ G))) (x : T ⟶ G)
    (hloc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over S) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ x) g = 0) :
    Triv (ev P (snd G T ≫ x) (fst G T)) := by
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (snd G T ≫ x) (fst G T))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (G ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (snd G T ≫ x) (fst G T)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd G T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hG T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, lift_snd_assoc, Category.id_comp, lift_fst]
    exact evc_one_right hP h2 x
  · intro p
    obtain ⟨V, hV, hz⟩ := hloc p
    refine ⟨V, hV, ?_⟩
    let U := (snd G T).left ⁻¹ᵁ V
    let Y : Over S := Over.mk (U.ι ≫ (G ⊗ T).hom)
    let i : Y ⟶ G ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, ← Category.assoc]
    exact hz Y _ _ (fun z ↦ z.2)

theorem triv_of_memKL_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  intro R _ _ G _ hG P hP h1 h2 hs T a b hx
  have hs' : (swap P).IsLB := pull_isLB hP _
  have h1' : Triv (ev P (1 : G ⟶ G) (𝟙 G)) := h1
  have h2' : Triv (ev P (𝟙 G) (1 : G ⟶ G)) := h2
  have add1 := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hG hG hP h1' h2')
  have add2 := (isAdditive_iff hs').1 (CubeNoeth.isAdditive_swap_of_triv_axes hG hG hP h1' h2')
  have symm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP v u = evc hP u v := by
    intro Y u v
    have e := congrArg (CechPic.pull (lift v u).left) ((cls_eq_iff hP hs').2 hs)
    exact e.trans (evc_swap hP hs' v u)
  have loc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over (Sp R)) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ a) g = 0 ∧ evc hP (t ≫ b) g = 0 := by
    intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    refine ⟨V, hV, fun Y t g ht ↦ ?_⟩
    have mk : ∀ u v : Y ⟶ G, evc hP ((t ≫ a) * u) ((t ≫ b) * v) = evc hP u v := by
      intro u v
      have e := pull_mul_eq hP hTV t ht (lift u v)
      have q : (t ≫ lift a b) * lift u v = lift ((t ≫ a) * u) ((t ≫ b) * v) := by
        ext <;> simp [MonObj.mul_comp]
      rw [q] at e
      exact e
    have e0 := mk 1 1
    rw [_root_.mul_one, _root_.mul_one, evc_one_left hP h1'] at e0
    constructor
    · have e1 := mk 1 g
      rw [_root_.mul_one, evc_one_left hP h1'] at e1
      have s := add2 Y (t ≫ b) g (t ≫ a)
      rw [evc_swap hP hs', evc_swap hP hs', evc_swap hP hs'] at s
      rw [s, e0, zero_add] at e1
      exact e1
    · have e3 := mk g 1
      rw [_root_.mul_one, evc_one_right hP h2'] at e3
      have s := add1 Y (t ≫ a) g (t ≫ b)
      rw [s, e0, zero_add] at e3
      rw [symm]
      exact e3
  refine ⟨triv_of_local_evc hG hP h2' a fun p ↦ ?_, triv_of_local_evc hG hP h2' b fun p ↦ ?_⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).1⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).2⟩

end GlobalTheory.KerAxes
