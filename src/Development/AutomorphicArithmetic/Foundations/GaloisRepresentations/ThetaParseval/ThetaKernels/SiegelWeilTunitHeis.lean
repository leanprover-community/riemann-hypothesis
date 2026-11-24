module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTparMain
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.DarbouxAnti
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem tHeis_k : _root_.PositivityTheory.SiegelWeilFormula.THeis_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ Z X
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, hf, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  set_option backward.isDefEq.respectTransparency false in
  constructor
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [Tpar.rho_rho (σ := σ) (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z * (incM F d.b.1.toCols₂)ᵀ) Φ, map_smul, smul_eq_mul]
    change d.B.ψ (⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _) * _ = _
    rw [symp_cols, frame_yy_A d.ok.frame, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.trace_zero, neg_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul, ← Matrix.add_mul]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [hBx, Matrix.transpose_mul, ← Matrix.mul_assoc, Tpar.rho_rho (σ := σ) (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z * (incM F t0.1)ᵀ * (diagCols (Fin d.n))ᵀ) Φ, map_smul, smul_eq_mul, add_comm,
      l_shift h hψ _ _ hΦ, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    change ⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _ + -(⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _) = _
    rw [darboux_anti d.dd, Matrix.mul_assoc Z, ← Matrix.transpose_mul, symp_cols, hf, Matrix.mul_one, trace_gram,
      map_neg]
    linear_combination (Algebra.trace (AF F) (AE F E) (Matrix.trace (Z * (X.map (cA σ))ᵀ * (incM F d.A.J)ᵀ))) *
      (invOf_two_add_invOf_two : (⅟(2 : AF F) + ⅟2 = 1))
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
