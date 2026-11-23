module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneDilV
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem inFrame_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) : inFrame d.b (R.ι w y) = Matrix.diagonal (dilV d.cm w i₀ τ) := by
  haveI := d.cm.1
  refine Place.mat_ext d.cm d.B.emb (fun u => ?_) ?_
  · have hD : (Matrix.diagonal (dilV d.cm w i₀ τ)).map (piInf (d.B.emb u)) =
        Matrix.diagonal (fun k => piInf (d.B.emb u) (dilV d.cm w i₀ τ k)) := Matrix.diagonal_map (map_zero _)
    rw [hD]
    simp_rw [piInf_dilV d.cm d.B.emb w u i₀ τ]
    by_cases hu : u = w
    · subst hu
      simp only [ite_true]
      have hat := R.at_w u y
      have hζ : R.ζ ≠ 0 := by
        rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
        · exact one_ne_zero
        · exact Complex.I_ne_zero
      have hZ : dZ d.n R.ζ⁻¹ * dZ d.n R.ζ = 1 := by
        simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
          add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hζ, mul_inv_cancel₀ hζ, one_smul,
          smul_zero, Matrix.fromBlocks_one]
      have e1 : d.cw u (inFrame d.b (R.ι u y)) = dZ d.n R.ζ⁻¹ * (mR y * dZ d.n R.ζ) := by
        rw [← hat, ← Matrix.mul_assoc, hZ, Matrix.one_mul]
      show d.cw u _ = _
      rw [e1, hy, ← Matrix.fromBlocks_diagonal]
      simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hζ, one_smul, Matrix.one_mul,
        smul_zero, mul_inv_cancel₀ hζ]
    · simp only [if_neg hu, Matrix.diagonal_one]
      exact R.off_w w u y hu
  · rw [R.off_f w y]
    ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with hij
    · subst hij; exact (finOne_dilV d.cm w i₀ τ i).symm
    · rfl
end PositivityTheory.SiegelWeilFormula.AStep
end
end
