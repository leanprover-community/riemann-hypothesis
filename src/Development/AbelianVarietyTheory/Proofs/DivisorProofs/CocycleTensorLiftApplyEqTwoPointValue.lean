module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.lift_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c)
    (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (φ ψ : G.A n →ₐ[R] D) :
    Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) =
      d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f (G.A n) D (toConv φ * toConv ψ).ofConv (t.y n) +
            (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f (G.A n) D φ (t.y n) + φ (d.h n)) -
          (fv d.f (G.A n) D ψ (t.y n) + ψ (d.h n))) := by
  set l : G.A n ⊗[R] G.A n →ₐ[R] D := Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) with hl
  have hc := (fv_isCoc_and_ev_eq R A d.f).1
  have e1 : l.comp Algebra.TensorProduct.includeLeft = φ := by
    simpa only [hl] using Algebra.TensorProduct.lift_comp_includeLeft φ ψ (fun _ _ ↦ Commute.all _ _)
  have e2 : l.comp Algebra.TensorProduct.includeRight = ψ := by
    simpa only [hl] using Algebra.TensorProduct.lift_comp_includeRight' φ ψ (fun _ _ ↦ Commute.all _ _)
  have e3 : l.comp (Bialgebra.comulAlgHom R (G.A n)) = (toConv φ * toConv ψ).ofConv := by
    apply AlgHom.ext
    intro a
    change l (Coalgebra.comul a) = (toConv φ * toConv ψ) a
    rw [AlgHom.convMul_apply, ofConv_toConv, ofConv_toConv, hl]
  have e4 : (toConv (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) *
      toConv Algebra.TensorProduct.includeRight).ofConv = Bialgebra.comulAlgHom R (G.A n) := by
    apply AlgHom.ext
    intro a
    simpa only [ofConv_toConv, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply,
      Bialgebra.comulAlgHom_apply]
      using AlgHom.convMul_apply
        (toConv (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n))
        (toConv Algebra.TensorProduct.includeRight) a
  have m := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
    (toConv Algebra.TensorProduct.includeRight)
  rw [e4] at m
  have a := d.add (G.A n ⊗[R] G.A n) D l (spOver Algebra.TensorProduct.includeLeft ≫ t.y n)
    (spOver Algebra.TensorProduct.includeRight ≫ t.y n)
  have c1 := hc _ _ _ Algebra.TensorProduct.includeLeft l (t.y n) (sm_whole _)
  have c2 := hc _ _ _ Algebra.TensorProduct.includeRight l (t.y n) (sm_whole _)
  have c3 := hc _ _ _ (Bialgebra.comulAlgHom R (G.A n)) l (t.y n) (sm_whole _)
  rw [← m, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e1, e2] at a
  rw [e1] at c1
  rw [e2] at c2
  rw [e3] at c3
  have h3 : l (Coalgebra.comul (d.h n)) = (toConv φ * toConv ψ).ofConv (d.h n) := by
    rw [← e3]; rfl
  have h1 : l (d.h n ⊗ₜ 1) = φ (d.h n) := by simp [hl]
  have h2 : l (1 ⊗ₜ d.h n) = ψ (d.h n) := by simp [hl]
  simp only [Dat.coc, cobOne_apply, map_sub, h1, h2, h3]
  rw [c1, c2, c3]
  linear_combination -a

end GlobalTheory.PtExt
