module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.WeylCubeConjUnipotent
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := by
  apply d.inFrame_inj
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [d.inFrame_mul, d.inFrame_mul, d.inFrame_mul, hW, d.inFrame_one, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_iota_pf (y : GR d.n) : d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  calc d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
        rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
    _ = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by rw [R.at_w w y, Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b w₀) = wM d.n ((ε : ℤ) : ℂ) := by
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [hW]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, wM, Matrix.one_apply] <;> split_ifs <;> simp
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt (x : Matrix (Fin d.n) (Fin d.n) ℂ) (hx : xᴴ = x) : GR d.n :=
  ⟨⟨nU x, nU (-x), by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one],
    by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]⟩,
    by
      show InG (nU x)
      simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hx]⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.nbar_conj_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, x, hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.oppositeUnipotent_weylConj {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ y' : GR d.n, mR y' = nU ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
