module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section

namespace GlobalTheory.LocOm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_inv_of_unit (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem nabs_pos_of_unit (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact NNReal.coe_pos.mpr distribHaarChar_pos

theorem linearFormula_inv_cancel {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (μS μT : kˣ →* ℂˣ)
    (gk : GL Y' k) (hk : GL Y k) (Φ : Matrix Y Y' k → ℂ) :
    (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk
      ((((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk⁻¹) : ℂˣ) : ℂ) • om μS⁻¹ gk⁻¹ hk⁻¹ Φ) = Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  have hx : ((↑(hk⁻¹⁻¹) : Matrix Y Y k) * ((↑(hk⁻¹) : Matrix Y Y k) * x * (↑gk : Matrix Y' Y' k)) *
      (↑(gk⁻¹) : Matrix Y' Y' k)) = x := by
    simp only [inv_inv, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hx]
  simp only [map_inv, nabs_inv_of_unit, Units.val_inv_eq_inv_val, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  have p1 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det gk)
  have p2 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det hk)
  rw [Real.inv_rpow p1.le, Real.inv_rpow p2.le]
  push_cast
  simp only [neg_div]
  have q1 : ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p1 _).ne'
  have q2 : ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-((Fintype.card Y' : ℝ) / 2)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p2 _).ne'
  have u1 := (μS (Matrix.GeneralLinearGroup.det gk)).ne_zero
  have u2 := (μS (Matrix.GeneralLinearGroup.det hk)).ne_zero
  have u3 := (μT (Matrix.GeneralLinearGroup.det gk)).ne_zero
  field_simp

theorem lawLoc_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k),
    LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g⁻¹ gk⁻¹ h⁻¹ hk⁻¹ := by
  intro D k _ _ _ _ S T ω μS μT Y Y' _ _ _ _ Tm g gk h hk hL Φ Φ' hΦ'
  have e : ω (g, h) (Tm Φ') = Tm Φ := hL Φ' Φ (by rw [hΦ', linearFormula_inv_cancel])
  rw [← e, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel]
  change ω 1 (Tm Φ') = Tm Φ'
  rw [map_one, Module.End.one_apply]

end GlobalTheory.LocOm

end
