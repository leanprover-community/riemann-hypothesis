module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.DZMulDZInv
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoLine

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem cw_mul' (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B := Matrix.map_mul

theorem cw_add' (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A + B) = d.cw w A + d.cw w B := Matrix.map_add _ (map_add _) A B

theorem cw_one' (w : InfinitePlace F) : d.cw w (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem cw_transpose' (w : InfinitePlace F) {p q : Type} (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ := rfl

theorem inFrame_mul' (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), _root_.PositivityTheory.SiegelWeilFormula.Krd.bb, Matrix.one_mul]

theorem inFrame_one' : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb']

theorem matrix_eq_frame_conj (x : d.G) : mat2 x = incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * inFrame d.b x *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
  simp only [inFrame, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb, Matrix.one_mul]

theorem cw_inFrame_prod' (R : RD d) (f : InfinitePlace F → GR d.n) (w' : InfinitePlace F) :
    ∀ L : List (InfinitePlace F), L.Nodup → d.cw w' (inFrame d.b ((L.map fun w => R.ι w (f w)).prod)) =
      if w' ∈ L then d.cw w' (inFrame d.b (R.ι w' (f w'))) else 1 := by
  intro L
  induction L with
  | nil => intro _; simp [inFrame_one', cw_one']
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, inFrame_mul', cw_mul', ih hL.2]
    by_cases h : w' = a
    · subst h
      simp [hL.1]
    · rw [R.off_w a w' (f a) h, Matrix.one_mul]
      simp [h]

theorem dZ_cw_rot' (R : RD d) (t : ℝ) (w : InfinitePlace F) :
    dZ d.n R.ζ * d.cw w (inFrame d.b (rot R t)) = yrotM d.n (R.sg w) t * dZ d.n R.ζ := by
  rw [rot, cw_inFrame_prod' R (fun w => yrot d.n (R.sg w) t) w _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ w)), R.at_w, mR_yrot]

end PositivityTheory.SiegelWeilFormula.KFP

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoLine =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoLine", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.DZMulDZInv\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem cw_line' (w : InfinitePlace F) (P Q : Mx F E d.m d.n) :
    d.cw w (P * (incM F d.b.1.toCols₂)ᵀ + Q * (incM F d.b.1.toCols₁)ᵀ) =
      Matrix.fromCols (d.cw w Q) (d.cw w P) * (d.cw w (incM F d.b.1))ᵀ := by
  rw [cw_add', cw_mul', cw_mul', cw_transpose', cw_transpose']
  conv_rhs => rw [← Matrix.fromCols_toCols (d.cw w (incM F d.b.1)), Matrix.transpose_fromCols,
    Matrix.fromCols_mul_fromRows]
  rw [add_comm]
  rfl

theorem cw_realAd_smul' (w : InfinitePlace F) {p q : Type} (r : ℝ) (X : Matrix p q (AE F E)) :
    d.cw w (realAd F r • X) = (r : ℂ) • d.cw w X :=
  GlobalTheory.RealScalar.realAd_smul_map σ d.B.emb d.cm X r w

theorem exp_mul_re' (t : ℝ) (z : ℂ) :
    (Complex.exp (-(t * Complex.I)) * z).re = z.re * Real.cos t + z.im * Real.sin t := by
  simp only [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [mul_zero, sub_zero, add_zero, mul_one, neg_zero, Real.exp_zero, one_mul,
    Real.cos_neg, Real.sin_neg]
  ring

theorem exp_mul_im' (t : ℝ) (z : ℂ) :
    (Complex.exp (-(t * Complex.I)) * z).im = z.im * Real.cos t - z.re * Real.sin t := by
  simp only [Complex.mul_im, Complex.exp_re, Complex.exp_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [mul_zero, sub_zero, add_zero, mul_one, neg_zero, Real.exp_zero, one_mul,
    Real.cos_neg, Real.sin_neg]
  ring

theorem finOne_smul_line' {W W' : Mx F E d.m d.n} (hW : finOne F • W = 0) (hW' : finOne F • W' = 0) (x y : ℝ) :
    finOne F • ((realAd F x • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F y • W') * (incM F d.b.1.toCols₁)ᵀ) = 0 := by
  rw [smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, smul_smul, smul_smul, mul_comm (finOne F),
    mul_comm (finOne F), ← smul_smul, ← smul_smul, hW, hW', smul_zero, smul_zero, Matrix.zero_mul,
    Matrix.zero_mul, add_zero]

theorem actB_rot_vline' (R : RD d) (t : ℝ) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) :
    actB (cA σ) (rot R t) (vline R W z) = vline R W (Complex.exp (-(t * Complex.I)) * z) := by
  have htw := (exists_tw R W).choose_spec
  have hζ : R.ζ ≠ 0 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  unfold vline
  rw [exp_mul_re', exp_mul_im']
  have hact : ∀ v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E), actB (cA σ) (rot R t) v = v * (mat2 (rot R t))ᵀ :=
    fun v => rfl
  rw [hact]
  refine Place.cw_ext (d := d) (fun w => ?_) ?_
  · rw [cw_mul', cw_transpose', matrix_eq_frame_conj, cw_mul', cw_mul', cw_line', cw_line', cw_realAd_smul', cw_realAd_smul',
      cw_realAd_smul', cw_realAd_smul', show d.cw w (tw R W) = _ from htw.2 w]
    have hinv : d.cw w (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) *
        d.cw w (incM F d.b.1) = 1 := by
      rw [← cw_mul', _root_.PositivityTheory.SiegelWeilFormula.Krd.bb', cw_one']
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ (d.cw w (incM F d.b.1))ᵀ, ← Matrix.transpose_mul, hinv, Matrix.transpose_one, Matrix.mul_one,
      rot_cols' d.n d.m hζ (R.sg w) t z.re z.im (d.cw w W) _ (dZ_cw_rot' R t w)]
  · rw [← Matrix.smul_mul, finOne_smul_line' (W' := tw R W) hW htw.1, finOne_smul_line' (W' := tw R W) hW htw.1,
      Matrix.zero_mul]

end PositivityTheory.SiegelWeilFormula.KFP

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoLine =====
