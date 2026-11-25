module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional, Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth, Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists, Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblSiegelX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def zs {n n₁ d : ℕ} (H : Plane E n n₁) (u : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Matrix.vecMulVec (incV F H.y) ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ u)

variable {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {d : ℕ}

end GlobalTheory.DblSiegelX
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchTraceNondeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cAinv (σ : E →ₐ[F] E) : AE F E →ₐ[AF F] AE F E :=
  Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F))
    (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩).symm.toAlgHom

end GlobalTheory.ArchTraceNondeg
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_one_tmul (e : E) : Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem eq_zero_of_psi_trace {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AE F E)
    (h : ∀ t : AE F E, ψ (Algebra.trace (AF F) (AE F E) (a * t)) = 1) : a = 0 := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bb : Module.Basis _ (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hco : ∀ i, ∀ x : AE F E, Algebra.trace (AF F) (AE F E) (x * ((1 : AF F) ⊗ₜ[F] b.traceDual i)) = bb.repr x i := by
    intro i x
    conv_lhs => rw [← bb.sum_repr x]

    rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, bb, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, trace_one_tmul, mul_comm (b _) (b.traceDual i), Module.Basis.trace_traceDual_mul]
    simp
  refine bb.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ
  intro y
  have := h (y • ((1 : AF F) ⊗ₜ[F] b.traceDual i))
  rwa [mul_smul_comm, map_smul, hco, smul_eq_mul, mul_comm] at this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def vdiff (σ : E →ₐ[F] E) {d : ℕ} (c : Fin d ⊕ Fin d → AE F E) : Fin d → AE F E :=
  fun l => cA σ (c (Sum.inl l)) - cA σ (c (Sum.inr l))

def pairL (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (c : Fin d ⊕ Fin d → AE F E) :
    (Fin d → AE F E) →ₗ[AF F] AF F where
  toFun u := Algebra.trace (AF F) (AE F E) (-1 * (u ⬝ᵥ (JW *ᵥ vdiff σ c)))
  map_add' u u' := by simp only [add_dotProduct, mul_add, map_add (f := _)]
  map_smul' r u := by simp only [smul_dotProduct, mul_smul_comm, map_smul, RingHom.id_apply]

end GlobalTheory.DblSiegelChar

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists =====

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.LagrangianProjectionFormula

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def pr (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (y : WOF F E nS nT) :
    (Fin (nT * nS) → AF F ⊗[F] E) →ₗ[AF F] AF F where
  toFun u := Algebra.trace (AF F) (AF F ⊗[F] E)
    (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace)
  map_add' u u' := by
    rw [map_add (f := _), Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, mul_add, map_add (f := _)]
  map_smul' r u := by
    have e : (vecE F E nS nT).symm (r • u) = r • (vecE F E nS nT).symm u := rfl
    rw [e, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, map_smul, RingHom.id_apply]

theorem pr_add (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (y y' : WOF F E nS nT) :
    pr σ JS ξ₀ (y + y') = pr σ JS ξ₀ y + pr σ JS ξ₀ y' := by
  refine LinearMap.ext fun u => ?_
  change Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      (((y + y').map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) =
    Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      ((y.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) +
    Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      ((y'.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace)
  rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, mul_add,
    map_add]

theorem phase_eq (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (hT : JT.det ≠ 0) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (y v : WOF F E nS nT) :
    phase σ JS JT ξ₀ ψ y v = ψ (pr σ JS ξ₀ y (vecE F E nS nT v)) := by
  unfold phase symplOF
  rw [hOF_dual JS JT hT]
  simp only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]

theorem pr_single (σ : E →ₐ[F] E) (hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (v : WOF F E nS nT) (k : Fin nT) (b : Fin nS) (z : AF F ⊗[F] E) :
    pr σ JS ξ₀ (Matrix.of fun i j => if i = k ∧ j = b then cAF σ z else 0) (vecE F E nS nT v) =
      Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (v * JS⁻¹.map (incAF F E)) k b * z) := by
  simp only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    apply_ite (cAF σ), map_zero, hcc, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem pr_sep (σ : E →ₐ[F] E) (hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (hS : JS.det ≠ 0) (ξ₀ : E) (hξ₀ : ξ₀ ≠ 0)
    (u : Fin (nT * nS) → AF F ⊗[F] E) (h : ∀ y : WOF F E nS nT, ψ (pr σ JS ξ₀ y u) = 1) : u = 0 := by
  set v := (vecE F E nS nT).symm u with hv
  have hu : u = vecE F E nS nT v := by rw [hv, AddEquiv.apply_symm_apply]
  have hw : ∀ k b, (v * JS⁻¹.map (incAF F E)) k b = 0 := by
    intro k b
    have h0 : incAF F E ξ₀ * (v * JS⁻¹.map (incAF F E)) k b = 0 := by
      apply GlobalTheory.DblSiegelChar.eq_zero_of_psi_trace hψ
      intro t
      have := h (Matrix.of fun i j => if i = k ∧ j = b then cAF σ t else 0)
      rwa [hu, pr_single σ hcc] at this
    have hunit : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 ξ₀ hξ₀).map (incAF F E)
    exact hunit.mul_right_eq_zero.1 h0
  have e1 : v * JS⁻¹.map (incAF F E) = 0 := by
    ext k b
    exact hw k b
  have e2 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul JS (Ne.isUnit hS), Matrix.map_one _ (map_zero _) (map_one _)]
  have hv0 : v = 0 := by
    calc v = v * JS⁻¹.map (incAF F E) * JS.map (incAF F E) := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
      _ = 0 := by rw [e1, Matrix.zero_mul]
  rw [hu, hv0, map_zero]

end PositivityTheory.ThKW.LagrangianProjectionFormula

end

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle =====
