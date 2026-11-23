module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInertStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAtStatement
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

namespace GlobalTheory.InertLagr

theorem exists_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
      ∃ Cy : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) G.W.J) Cy := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw
  have hF := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hT.base v w hvw
  obtain ⟨y, u, hu, hy⟩ := GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert F E σ B hT.base _ _ _ G.W hT.geo.hW hT.geo.even v w hvw hF
  obtain ⟨z, hz⟩ := GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt F E σ B hT.base v w hvw hF u hu
  refine GlobalTheory.T.exists_lagrangian_skewHermitian_completionTensor F E σ hT.base.cm v hF (a + a') G.W.J hT.geo.even hT.geo.hW.skew
    (GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace F E σ B _ _ _ G.W hT.geo.hW) ⟨z * y, ?_⟩
  rw [hy, hz, map_mul]
  ring

end GlobalTheory.InertLagr
