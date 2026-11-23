module

public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
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

namespace GlobalTheory.AbDual

theorem memKL_lift_one_of_triv_ev : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  intro R _ _ G _ hG P hP h0l h0r _ T a ha
  have hadd : IsAdditive P := CubeNoeth.isAdditive_of_triv_axes hG hG hP h0l h0r
  have hD : (Out.translDiff (G ⊗ G) P (lift a (1 : T ⟶ G))).IsLB := LB.isLB_linComb hP _ _
  have hz : cls _ hD = 0 := by
    have e₁ := pull_translDiff hP (lift a (1 : T ⟶ G)) hD (fst T (G ⊗ G)) (snd T (G ⊗ G))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have em : (fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G) =
        lift ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp [MonObj.mul_comp]
    have eu : snd T (G ⊗ G) = lift (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp
    have k₁ : CechPic.pull ((fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G)).left (cls P hP) =
        evc hP ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [em]; rfl
    have k₂ : CechPic.pull (snd T (G ⊗ G)).left (cls P hP) =
        evc hP (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [evc, ← eu]
    have k₃ : evc hP (fst T (G ⊗ G) ≫ a) (snd T (G ⊗ G) ≫ snd G G) = 0 := by
      have e := congrArg (CechPic.pull (lift (snd T (G ⊗ G) ≫ snd G G) (fst T (G ⊗ G))).left)
        ((triv_ev_iff hP _ _).1 ha)
      rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
    rw [e₁, k₁, k₂, (isAdditive_iff hP).1 hadd, add_sub_cancel_right, k₃]
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, hz, map_zero]

end GlobalTheory.AbDual
