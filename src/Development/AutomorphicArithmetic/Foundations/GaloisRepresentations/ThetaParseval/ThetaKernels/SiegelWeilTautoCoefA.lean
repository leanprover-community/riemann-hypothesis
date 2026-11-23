module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTbBdd
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E) : Mx F E d.m d.n := mat g⁻¹ * incM F X
theorem cont_tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    Continuous fun g : UA σ d.A.J => f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) := by
  have h1 : Continuous (f ∘ d.cmb) := PositivityTheory.ThKEst.continuous_schA (Φ := f ∘ d.cmb) hf
  have e : ∀ Y, f Y = (f ∘ d.cmb) (d.crd Y) := fun Y => by simp [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_crd_k]
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k, e, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k]
  exact h1.comp (((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mh_k d).comp h2).matrix_mulVec continuous_const)
theorem chr_comb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (β G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * G))) * d.B.ψ (-(d.tt (T * β))) =
      d.B.ψ (-(d.tt ((⅟(2 : AF F) • G + T) * β))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul, map_add (f := _), map_smul, smul_eq_mul,
    Matrix.trace_mul_comm G β]
  ring
theorem half_eq_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    ⅟(2 : AF F) • G + T = 0 ↔ G = (-2 : ℤ) • T := by
  have h2 : algebraMap (AF F) (AE F E) ⅟(2 : AF F) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def] at this
    rw [Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination 2 * this - G i j * h2
  · rintro rfl
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination (-T i j) * h2
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
