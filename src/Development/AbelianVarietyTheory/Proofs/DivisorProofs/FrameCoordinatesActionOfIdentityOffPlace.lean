module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem frame_mul_map (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) L) (Y : Matrix (Fin m) (Fin k) L) :
    ((1 - ι 1) • (1 : Matrix (Fin m) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι) * Y.map ι = (A * Y).map ι := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j

  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
  zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, hmul]

theorem map_mul_frame_transpose (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (C : Matrix (Fin k) (Fin k) L) (Y : Matrix (Fin m) (Fin k) L) :
    Y.map ι * ((1 - ι 1) • (1 : Matrix (Fin k) (Fin k) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι)ᵀ = (Y * Cᵀ).map ι := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  ext i j

  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
  zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, Matrix.transpose_apply, hmul]

theorem actAB_xm_frame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
    (g : UA σ X.J) (h : UA σ W.J)
    (hg : mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι)
    (hh : mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι) (x : Matrix (Fin d) (Fin n) L) :
    actAB (cA σ) (g, h) (xm ι PV PW x) =
      (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  change mat g * xm ι PV PW x * (mat h)ᵀ = _
  rw [xm_apply, hg, hh, frame_mul_map ι hmul, map_mul_frame_transpose ι hmul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.InertLocFrame

end
