module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)
open scoped TensorProduct
open GroundTheory.Global.SemiLocal

noncomputable section

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem lies {v : Pl (Lp L)} {w : Plc L} (h : un w = v) : w.asIdeal.LiesOver v.asIdeal := by
  subst h
  exact ⟨rfl⟩

private theorem unOf {v : Pl (Lp L)} {w : Plc L} (h : w.asIdeal.LiesOver v.asIdeal) : un w = v :=
  HeightOneSpectrum.ext h.over.symm

private theorem phi_eq (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v)
    [w.asIdeal.LiesOver v.asIdeal] (a : Kv v) : P.φ v w h a = completionMap v w a := by
  have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 (Lp L)) (Lp L) v
  have key : (P.φ v w h) ∘ algebraMap (Lp L) (Kv v) =
      (completionMap v w) ∘ algebraMap (Lp L) (Kv v) := by
    funext x
    simp only [Function.comp_apply]
    rw [completionMap_algebraMap]
    exact (P.φ_alg v w h x).trans (IsScalarTower.algebraMap_apply (Lp L) L _ x).symm
  exact congrFun (hd.equalizer (P.φ_cont v w h) (continuous_completionMap v w) key) a

private def bas (P : Pre L) : Module.Basis (Fin 2) (Lp L) L :=
  (QuadraticAlgebra.basis P.Δ 0).map (AlgEquiv.ofRingEquiv (f := P.e) P.e_alg).toLinearEquiv

private def ttEquiv (P : Pre L) (v : Pl (Lp L)) :
    Lsq (Kv v) (cv v P.Δ) ≃ₗ[Kv v] Kv v ⊗[Lp L] L :=
  (QuadraticAlgebra.linearEquivTuple (cv v P.Δ) 0).trans
    (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm

private theorem ttEquiv_apply (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ))
    (p : PlacesOver L v) :
    tensorEquiv L v (ttEquiv P v x) p = P.rho v p.1 (unOf p.2) x := by
  have htt : ttEquiv P v x = x.re ⊗ₜ 1 + x.im ⊗ₜ P.e QuadraticAlgebra.omega := by
    rw [ttEquiv, LinearEquiv.trans_apply, QuadraticAlgebra.linearEquivTuple_apply,
      Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
    simp only [Algebra.TensorProduct.basis_apply, bas, Module.Basis.map_apply,
      QuadraticAlgebra.basis_apply_zero, QuadraticAlgebra.basis_apply_one,
      AlgEquiv.coe_toLinearEquiv, map_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  simp only [htt, map_add (f := _), tensorEquiv_tmul, map_one, mul_one, Pi.add_apply, Pi.mul_apply]
  haveI := p.2
  show completionMap v p.1 x.re +
      completionMap v p.1 x.im * algebraMap L _ (P.e QuadraticAlgebra.omega) =
    P.φ v p.1 (unOf p.2) x.re + P.φ v p.1 (unOf p.2) x.im * P.rt p.1
  rw [phi_eq P v p.1 (unOf p.2), phi_eq P v p.1 (unOf p.2)]
  rfl

end UpperTheory.V.Z.Sym.Dict.Br

end

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoBij :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v : Pl (Lp L), Function.Bijective fun (x : Lsq (Kv v) (cv v P.Δ)) (w : {w : Plc L // un w = v}) => P.rho v w.1 w.2 x := by
  intro L _ _ _ P v
  constructor
  · intro x y hxy
    refine (ttEquiv P v).injective ((tensorEquiv L v).injective (funext fun p => ?_))
    rw [ttEquiv_apply, ttEquiv_apply]
    exact congrFun hxy ⟨p.1, unOf p.2⟩
  · intro f
    obtain ⟨t, ht⟩ := (tensorEquiv L v).surjective (fun p => f ⟨p.1, unOf p.2⟩)
    obtain ⟨x, rfl⟩ := (ttEquiv P v).surjective t
    refine ⟨x, funext fun w => ?_⟩
    have := congrFun ht ⟨w.1, lies w.2⟩
    rw [ttEquiv_apply] at this
    exact this
