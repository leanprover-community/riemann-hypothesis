module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G]

theorem lam_inv_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) :
    lam (cls L hL) x⁻¹ z = - lam (cls L hL) x z := by
  have h := lam_mul_left hL hΘ x⁻¹ x z
  rw [inv_mul_cancel, lam_one_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem lam_inv_inv {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) :
    lam (cls L hL) x⁻¹ y⁻¹ = lam (cls L hL) x y := by
  rw [lam_inv_left hL hΘ, lam_comm, lam_inv_left hL hΘ, lam_comm, neg_neg]

theorem lam_pull_inv (c : Pic G.left) (x y : T ⟶ G) :
    lam (pull (ι[G]).left c) x y = lam c x⁻¹ y⁻¹ := by
  simp only [lam, ← pull_comp, ← Over.comp_left, ← Hom.inv_def, mul_inv, inv_one]

end GlobalTheory.PolDeg.NegPrim

namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

theorem lam_negPull_sub_isTrivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  intro A _ _ _ B _ _ M cub _
  have hΘ : ∃ t : LB.Gen (Theta B M.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  have hN : (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).IsLB := LB.isLB_linComb M.isLB _ _
  have hΛ : (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])).IsLB := LB.isLB_linComb hN _ _
  refine (cls_eq_zero_iff hΛ).1 ?_
  have hc : cls _ hN = pull (ι[B]).left (cls M.L M.isLB) - cls M.L M.isLB := by
    rw [cls_linComb M.isLB, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, sub_eq_add_neg]
  refine (cls_cube_two hN (fst B B) (snd B B) hΛ).trans ?_
  have e : ∀ (c c' : Pic B.left) (x y : B ⊗ B ⟶ B), lam (c - c') x y = lam c x y - lam c' x y := fun c c' x y => by
    simp only [lam, map_sub]; abel
  rw [hc, e, lam_pull_inv, lam_inv_inv M.isLB hΘ, sub_self]

end GlobalTheory.PolDeg.NegPrim
