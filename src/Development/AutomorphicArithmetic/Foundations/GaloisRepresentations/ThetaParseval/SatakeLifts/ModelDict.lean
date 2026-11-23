module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.modelDict :
    UpperTheory.Gal.TP.Loc.ModelDict := by
  intro k _ _ _ _ n d ν b g h Ψ X
  have hM : ((((GlobalTheory.SplitFlip.invT g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      ((GlobalTheory.SplitFlip.invT h : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)).transpose =
      ((h⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) * X.transpose * (g : Matrix (Fin n) (Fin n) k) := by
    rw [GlobalTheory.SplitFlip.invT_inv_val, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hg := nabs_pos k (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos k (Matrix.GeneralLinearGroup.det h)
  unfold GlobalTheory.SplitFlip.omA om
  rw [GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv]
  beta_reduce
  rw [hM]
  simp only [GlobalTheory.SplitFlip.apow, GlobalTheory.SplitFlip.gdet, Fintype.card_fin]
  rw [Complex.ofReal_cpow hg.le, Complex.ofReal_cpow hh.le]
  simp only [map_inv, inv_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    neg_div, neg_neg, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hb : ((b (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
