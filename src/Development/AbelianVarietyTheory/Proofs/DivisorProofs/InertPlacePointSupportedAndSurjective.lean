module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoord

theorem kap_at_and_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  intro F E _ _ _ _ _ v w hw h m n A Bm
  refine ⟨fun x u hu => ?_, fun γ hγ => ?_⟩
  · ext i j
    rw [Matrix.smul_apply, kap_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  · refine ⟨(((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ))ᵀ, ?_⟩
    rw [kap_apply, Matrix.transpose_transpose]
    have e : (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *
        (((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = γ.map (locW h) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    rw [e]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    refine ptAt_locW hw h fun u hu => ?_
    have := congrFun (congrFun (hγ u hu) i) j
    rwa [Matrix.smul_apply, Matrix.zero_apply] at this

end GlobalTheory.InertCoord
