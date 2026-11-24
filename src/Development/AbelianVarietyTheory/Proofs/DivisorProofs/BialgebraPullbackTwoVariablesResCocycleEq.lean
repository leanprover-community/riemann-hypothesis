module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.fv_add_h_res {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}
    {t : G.TorsionTower A} {c : primDR A} (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D]
    (φ : G.A n →ₐ[R] D) :
    fv d.f (G.A (n + 1)) D (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (t.y (n + 1)) +
      (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (d.h (n + 1)) = fv d.f (G.A n) D φ (t.y n) + φ (d.h n) := by
  have hc := (fv_isCoc_and_ev_eq R A d.f).1 (G.A (n + 1)) (G.A n) D
    (G.res n : G.A (n + 1) →ₐ[R] G.A n) φ (t.y (n + 1)) (sm_whole (t.y (n + 1)))
  rw [hc, t.res n, d.res n, AlgHom.comp_apply, map_sub]
  simp only [BialgHom.coe_toAlgHom]
  abel

theorem Dat.pullTwo_res_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n := by
  let L : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeLeft
  let Rt : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeRight
  have hres : ∀ u : G.A (n + 1) ⊗[R] G.A (n + 1), pullbackTwo (G.res n) u =
      Algebra.TensorProduct.lift (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))
        (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (fun _ _ ↦ Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a b => simp [L, Rt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hid : ∀ u : G.A n ⊗[R] G.A n,
      Algebra.TensorProduct.lift L Rt (fun _ _ ↦ Commute.all _ _) u = u := by
    intro u
    simp only [L, Rt, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply]
  have hmul : (toConv (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) *
      toConv (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))).ofConv =
      (toConv L * toConv Rt).ofConv.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n) :=
    (AlgHom.convMul_comp_bialgHom_distrib (toConv L) (toConv Rt) (G.res n)).symm
  rw [hres, Dat.lift_coc, hmul, d.fv_add_h_res n, d.fv_add_h_res n, d.fv_add_h_res n]
  conv_rhs => rw [← hid (d.coc n), Dat.lift_coc]
  simp only [← spOver_comp, Category.assoc, t.res]

end GlobalTheory.PtExt
