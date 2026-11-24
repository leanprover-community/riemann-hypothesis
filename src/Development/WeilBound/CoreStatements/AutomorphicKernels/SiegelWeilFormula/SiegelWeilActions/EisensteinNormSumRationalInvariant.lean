module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousNilpotentFramePart
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzEqFlat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.IsUnitDetInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.HomExtensionByZeroOrthDecompRational
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinRationalInvariantReindex, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinNormSumRationalInvariant

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinRationalInvariantReindex =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinRationalInvariantReindex", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousNilpotentFramePart\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzEqFlat\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ}

variable {R : RD d} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem lagrangian_condition_mul_fixing {γ r : d.G}
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) :
    LagrangianCondition L (γ * r) ↔ LagrangianCondition L γ := by
  have e : ∀ i, inFrame d.b (γ * r) (Sum.inr i) (Sum.inl L.i₀) = inFrame d.b γ (Sum.inr i) (Sum.inl L.i₀) := by
    intro i
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
    simp only [hx, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [LagrangianCondition, e]

theorem lagrangian_condition_stabiliser_iff {p g : d.G} (hp : p ∈ par2 σ d.Y) : LagrangianCondition L (p * g) ↔ LagrangianCondition L g := by
  have h21 : ∀ {q : d.G}, q ∈ par2 σ d.Y → ∀ i j, inFrame d.b q (Sum.inr i) (Sum.inl j) = 0 := by
    intro q hq i j
    have := (kunf.mem_stabiliser_iff_frame_lower_block d.ok.frame q).1 hq
    have := congrFun (congrFun this i) j
    simpa [Matrix.toBlocks₂₁] using this
  have key : ∀ {q γ : d.G}, q ∈ par2 σ d.Y → LagrangianCondition L γ → LagrangianCondition L (q * γ) := by
    intro q γ hq hγ i
    have hγ' : ∀ k, inFrame d.b γ (Sum.inr k) (Sum.inl L.i₀) = 0 := hγ
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [h21 hq, hγ']
  refine ⟨fun h => ?_, key hp⟩
  have := key (inv_mem hp) h
  rwa [inv_mul_cancel_left] at this

theorem eisenstein_sum_reindex {M : Type} [AddCommMonoid M] [TopologicalSpace M] (H : ℂ → M) {s₁ : ℂ} {f : d.G → ℂ}
    (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, H (phz d f s₁ z (rep q.1 * (r * g))) =
      ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, H (phz d f s₁ z (rep q.1 * g)) := by
  classical
  let γr : rat2 σ d.Y := ⟨r, hr⟩
  let e0 := GlobalTheory.Eis.rmulEquiv (par2 σ d.Y) (rat2 σ d.Y) γr
  have hrep : ∀ q : Cs d, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ rep (e0 q) = p * (rep q * r) := by
    intro q
    have h1 : e0 q = GlobalTheory.AutomorphicL2Unitary.mk _ (Quotient.out q * γr) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ γr q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    have h2 : GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) (Quotient.out q * γr) =
        GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) (Quotient.out (e0 q)) := by
      rw [← h1]; exact (Quotient.out_eq _).symm
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h2
    refine ⟨((γ : rat2 σ d.Y) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : rat2 σ d.Y).2, ?_⟩
    have := congrArg Subtype.val hγ
    show ((Quotient.out (e0 q) : rat2 σ d.Y) : d.G) = _
    rw [← this]
    rfl
  have hS : ∀ q : Cs d, ¬ LagrangianCondition L (rep q) ↔ ¬ LagrangianCondition L (rep (e0 q)) := by
    intro q
    obtain ⟨p, hp, -, he⟩ := hrep q
    rw [he, lagrangian_condition_stabiliser_iff hp, lagrangian_condition_mul_fixing hx]
  let e : {q : Cs d // ¬ LagrangianCondition L (rep q)} ≃ {q : Cs d // ¬ LagrangianCondition L (rep q)} := e0.subtypeEquiv hS
  have hterm : ∀ q : {q : Cs d // ¬ LagrangianCondition L (rep q)},
      phz d f s₁ z (rep q.1 * (r * g)) = phz d f s₁ z (rep (e q).1 * g) := by
    intro q
    obtain ⟨p, hp, hpr, he⟩ := hrep q.1
    show _ = phz d f s₁ z (rep (e0 q.1) * g)
    rw [he, mul_assoc, mul_assoc, C4.phz_rat hf z hp hpr]
  rw [tsum_congr fun q => congrArg H (hterm q)]
  exact e.tsum_eq (fun q => H (phz d f s₁ z (rep q.1 * g)))

theorem eisenstein_rational_invariant_reindex {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : E2 L (phz d f s₁ z) (r * g) = E2 L (phz d f s₁ z) g :=
  eisenstein_sum_reindex id hf z hr hx g

theorem eisenstein_norm_sum_reindex {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (r * g))‖ₑ =
      ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * g)‖ₑ :=
  eisenstein_sum_reindex (fun w => ‖w‖ₑ) hf z hr hx g

def eO (L : LD d) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ 1

theorem em_ne' (L : LD d) (j : Fin L.n) : L.i₀ ≠ L.em j := (ComplexParameterFamilyContinuity.em_ne L j).symm

theorem eO_mul_eO : eO L * eO L = eO L := by
  simp [eO]

theorem eO_single (x : AE F E) : eO L * Matrix.single L.i₀ L.i₀ x = Matrix.single L.i₀ L.i₀ x := by
  simp [eO]

theorem single_eO (x : AE F E) : Matrix.single L.i₀ L.i₀ x * eO L = Matrix.single L.i₀ L.i₀ x := by
  simp [eO]

theorem wf_blocks (α β : AE F E) :
    (1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 - Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 +
      Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) α + Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) β :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - eO L) := by
  ext (i | i) (j | j) <;> simp [eO, Matrix.single, Matrix.one_apply]

theorem wf_mul (α β α' β' : AE F E) (ha : α * α' = 1) (hb : β * β' = 1) :
    Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - eO L) *
      Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ β') (Matrix.single L.i₀ L.i₀ α') (1 - eO L) = 1 := by
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have h1 : (1 - eO L) * (1 - eO L) = 1 - eO L := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, eO_mul_eO]; abel
  congr 1
  · rw [h1, Matrix.single_mul_single_same, ha, ← eO]; abel
  · simp only [mul_sub, sub_mul, one_mul, mul_one, eO_single, single_eO]; abel
  · simp only [mul_sub, sub_mul, one_mul, mul_one, eO_single, single_eO]; abel
  · rw [h1, Matrix.single_mul_single_same, hb, ← eO]; abel

theorem det_one_add_col (N : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hN : ∀ i j, j ≠ L.i₀ → N i j = 0)
    (h0 : N L.i₀ L.i₀ = 0) : (1 + N).det = 1 := by
  have e : N = Matrix.replicateCol Unit (fun i => N i L.i₀) * Matrix.replicateRow Unit (Pi.single L.i₀ (1 : AE F E)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    by_cases hj : j = L.i₀
    · subst hj; simp
    · rw [hN i j hj]; simp [hj]
  rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [h0]

theorem section_w1_siegel_invariant_of_hyp (h : Hyp L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    (b : Fin L.n → AE F E) (g : d.G) : phz d f s₁ z (w₁ * (sM R L b * g)) = phz d f s₁ z (w₁ * g) := by
  classical
  obtain ⟨a₁, b₁, ha₁, hb₁, hW⟩ := h.wf
  set α : AE F E := inclR (F := F) (AF F) a₁
  set β : AE F E := inclR (F := F) (AF F) b₁
  set α' : AE F E := inclR (F := F) (AF F) a₁⁻¹
  set β' : AE F E := inclR (F := F) (AF F) b₁⁻¹
  have hα : α * α' = 1 := by rw [← map_mul, mul_inv_cancel₀ ha₁, map_one]
  have hβ : β * β' = 1 := by rw [← map_mul, mul_inv_cancel₀ hb₁, map_one]
  set W := Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - eO L)
  set W' := Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ β') (Matrix.single L.i₀ L.i₀ α') (1 - eO L)
  have hW1 : inFrame d.b w₁ = W := by rw [hW, wf_blocks]
  have hWW : W * W' = 1 := wf_mul α β α' β' hα hβ
  have hWi : inFrame d.b w₁⁻¹ = W' := by
    have h1 : inFrame d.b w₁⁻¹ * W = 1 := by rw [← hW1, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    calc inFrame d.b w₁⁻¹ = inFrame d.b w₁⁻¹ * (W * W') := by rw [hWW, Matrix.mul_one]
      _ = W' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  set S := sB R L b
  set p : d.G := w₁ * sM R L b * w₁⁻¹
  have hP : inFrame d.b p = W * bMat S * W' := by
    simp only [p, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hW1, hWi, inFrame_sM']
    rfl
  have hS0 : S L.i₀ L.i₀ = 0 := sB_i0i0 b
  have h1e : (1 - eO L) * (1 - eO L) = 1 - eO L := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, eO_mul_eO]; abel
  have h21 : (inFrame d.b p).toBlocks₂₁ = 0 := by
    rw [hP]
    simp only [W, W', bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
    rw [add_mul, Matrix.single_mul_mul_single, hS0, mul_sub, mul_one, single_eO, sub_mul, one_mul, eO_single]
    simp
  set N := (1 - eO L) * S * Matrix.single L.i₀ L.i₀ α'
  have h11 : (inFrame d.b p).toBlocks₁₁ = 1 + N := by
    rw [hP]
    simp only [W, W', bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
    rw [h1e, add_mul, Matrix.single_mul_single_same, hα, ← eO]
    simp only [N]; abel
  have hN : ∀ i j, j ≠ L.i₀ → N i j = 0 := fun i j hj => by
    simp only [N]; exact Matrix.mul_single_apply_of_ne _ _ _ _ _ hj _
  have hN0 : N L.i₀ L.i₀ = 0 := by
    simp only [N, Matrix.mul_single_apply_same, sub_mul, one_mul, Matrix.sub_apply, eO, Matrix.single_mul_apply_same,
      one_mul, sub_self]
  have hp : p ∈ par2 σ d.Y := (kunf.mem_stabiliser_iff_frame_lower_block d.ok.frame p).2 h21
  obtain ⟨t, ht⟩ := GlobalTheory.ThK.Dbl.mem_parabolic_GL2_iff.1 hp
  obtain ⟨-, t₀, ht₀⟩ := d.ok.frame
  have htv := ((kunf.isPar_frame ht₀ p t).1 ht).2
  have hdet : Matrix.GeneralLinearGroup.det t = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, htv, Matrix.det_mul, Matrix.det_mul, h11, det_one_add_col N hN hN0,
      mul_one, Units.val_one, ← Matrix.det_mul, kunf.incM_GL_mul_inv, Matrix.det_one]
  have hg : w₁ * (sM R L b * g) = p * (w₁ * g) := by simp only [p]; group
  rw [hg, C4.phz_par hf z ht hdet]

theorem ratV_incl {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    ∃ x : Fin L.n → E, v = fun i => inclR (F := F) (AF F) (x i) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv => obtain ⟨x, hx⟩ := hv; exact ⟨x, by rw [← hx]; rfl⟩
  | zero => exact ⟨0, by ext i; simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨x, rfl⟩ := hv; obtain ⟨x', rfl⟩ := hw; exact ⟨x + x', by ext i; simp⟩
  | neg v _ hv => obtain ⟨x, rfl⟩ := hv; exact ⟨-x, by ext i; simp⟩

theorem hz_uA_i0i0 (u : Fin L.n → AE F E) : uA L u L.i₀ L.i₀ = 1 := by
  simp [uA, Matrix.sum_apply, Matrix.single, ComplexParameterFamilyContinuity.em_ne L]

theorem hz_uA_i0em (u : Fin L.n → AE F E) (l : Fin L.n) : uA L u L.i₀ (L.em l) = u l := by
  simp [uA, Matrix.sum_apply, Matrix.single, em_ne' L, L.inj.eq_iff]

theorem unipotent_block_embedded_zero (u : Fin L.n → AE F E) (k : Fin L.n) : uA L u (L.em k) L.i₀ = 0 := by
  simp [uA, Matrix.sum_apply, Matrix.single, ComplexParameterFamilyContinuity.em_ne L, em_ne' L]

theorem hz_uA_emem (u : Fin L.n → AE F E) (k l : Fin L.n) :
    uA L u (L.em k) (L.em l) = if k = l then 1 else 0 := by
  simp [uA, Matrix.sum_apply, Matrix.single, Matrix.one_apply, em_ne' L, L.inj.eq_iff]

def Dm (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (uA L (-u))ᵀ.map (cA σ)

theorem hz_D_i0i0 (u : Fin L.n → AE F E) : Dm L u L.i₀ L.i₀ = 1 := by
  simp [Dm, hz_uA_i0i0]

theorem hz_D_i0em (u : Fin L.n → AE F E) (l : Fin L.n) : Dm L u L.i₀ (L.em l) = 0 := by
  simp [Dm, unipotent_block_embedded_zero]

theorem diagonal_block_embedded_neg_conj (u : Fin L.n → AE F E) (k : Fin L.n) : Dm L u (L.em k) L.i₀ = -cA σ (u k) := by
  simp [Dm, hz_uA_i0em]

theorem hz_D_emem (u : Fin L.n → AE F E) (k l : Fin L.n) : Dm L u (L.em k) (L.em l) = if k = l then 1 else 0 := by
  simp only [Dm, Matrix.map_apply, Matrix.transpose_apply, hz_uA_emem]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl, Ne.symm hkl]

theorem hz_aB_i0i0 (x : AF F) : aB L δ x L.i₀ L.i₀ = x • inclR (F := F) (AF F) δ := by
  simp [aB, Matrix.single]

theorem hz_aB_i0em (x : AF F) (l : Fin L.n) : aB L δ x L.i₀ (L.em l) = 0 := by
  simp [aB, Matrix.single, em_ne' L]

theorem centre_block_embedded_zero (x : AF F) (k : Fin L.n) : aB L δ x (L.em k) L.i₀ = 0 := by
  simp [aB, Matrix.single, em_ne' L]

theorem hz_aB_emem (x : AF F) (k l : Fin L.n) : aB L δ x (L.em k) (L.em l) = 0 := by
  simp [aB, Matrix.single, em_ne' L]

theorem hz_uA_add (u v : Fin L.n → AE F E) : uA L u * uA L v = uA L (u + v) := by
  have e := ComplexParameterFamilyContinuity.nilpotent_frame_mul_zero L u v
  change (1 + ComplexParameterFamilyContinuity.nilpotentFrameMatrix L u) * (1 + ComplexParameterFamilyContinuity.nilpotentFrameMatrix L v) = 1 + ComplexParameterFamilyContinuity.nilpotentFrameMatrix L (u + v)
  rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, e, add_zero]
  simp only [ComplexParameterFamilyContinuity.nilpotentFrameMatrix, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]
  abel

theorem heis' (h : Hyp L nb uM nb' w₁ cM δ) :
    ∃ Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F, Continuous (Function.uncurry Z) ∧
      (∀ u₀ b, u₀ ∈ L.ratV → b ∈ L.ratV → Z u₀ b ∈ (algebraMap F (AF F)).range) ∧
      ∀ u₀ a₀ b u a, cM (u₀, a₀) * (sM R L b * cM (u, a)) = sM R L b * cM (u₀ + u, a₀ + a + Z u₀ b) := by
  classical
  let y : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AE F E := fun u₀ b =>
    ∑ l, b l * cA σ (u₀ l) - ∑ k, u₀ k * (eA R * cA σ (b k))
  refine ⟨fun u₀ b => ellA δ (y u₀ b), ?_, ?_, ?_⟩
  · have hl : Continuous (ellA (F := F) (E := E) δ) := IsModuleTopology.continuous_of_linearMap _
    have hc := GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ
    show Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => ellA δ (y p.1 p.2)
    refine hl.comp ((continuous_finsetSum _ fun l _ => ?_).sub (continuous_finsetSum _ fun k _ => ?_))
    · exact ((continuous_apply l).comp continuous_snd).mul (hc.comp ((continuous_apply l).comp continuous_fst))
    · exact ((continuous_apply k).comp continuous_fst).mul
        (continuous_const.mul (hc.comp ((continuous_apply k).comp continuous_snd)))
  · intro u₀ b hu hb
    obtain ⟨x0, rfl⟩ := ratV_incl hu
    obtain ⟨xb, rfl⟩ := ratV_incl hb
    have hc (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have e : y (fun i => inclR (F := F) (AF F) (x0 i)) (fun i => inclR (F := F) (AF F) (xb i)) =
        inclR (F := F) (AF F) (∑ l, xb l * σ (x0 l) - ∑ k, x0 k * (((R.ε : ℤ) : E) * σ (xb k))) := by

      simp only [y, eA, map_sub, map_sum, map_mul, hc]
    show ellA δ (y _ _) ∈ _
    rw [e]
    exact ellA_inclR h _
  · intro u₀ a₀ b u a
    have hC : ∀ c, inFrame d.b (cM c) = Matrix.fromBlocks (uA L c.1) (aB L δ c.2) 0 (Dm L c.1) := inFrame_cM h
    have hM := inFrame_sM' (R := R) (L := L) b
    apply eq_of_upper
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hM]
      simp [bMat, Matrix.fromBlocks_multiply]
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hM]
      simp [bMat, Matrix.fromBlocks_multiply]
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hC, hM]
      simp only [bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      exact hz_uA_add u₀ u
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hC, hM]
      simp only [bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      have hZ : ellA δ (y u₀ b) • inclR (F := F) (AF F) δ = y u₀ b := by
        refine eig (R := R) h _ ?_
        have he := eps_mul R

        simp only [y, eA_eq, map_sub, map_sum, map_mul, map_intCast, cc d, mul_sub, Finset.mul_sum]
        simp only [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (-(u₀ l * cA σ (b l))) * he
      ext i j
      rcases idx L i with rfl | ⟨k, rfl⟩ <;> rcases idx L j with rfl | ⟨l, rfl⟩ <;>
        simp only [Matrix.add_apply, Matrix.mul_apply, sum_split L, hz_uA_i0i0, hz_uA_i0em, unipotent_block_embedded_zero, hz_uA_emem,
          hz_D_i0i0, hz_D_i0em, diagonal_block_embedded_neg_conj, hz_D_emem, hz_aB_i0i0, hz_aB_i0em, centre_block_embedded_zero, hz_aB_emem, sB_i0i0,
          sB_i0em, siegel_block_embedded_row, sB_emem, Pi.add_apply, map_add, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
          mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      rw [add_smul, add_smul, hZ]
      simp only [y, mul_neg, mul_add, neg_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]
      ring

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinRationalInvariantReindex =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinNormSumRationalInvariant =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinNormSumRationalInvariant", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.IsUnitDetInFrame\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousNilpotentFramePart\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinRationalInvariantReindex\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.HomExtensionByZeroOrthDecompRational\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

theorem uA_zero : uA L 0 = 1 := by simp [uA]

theorem uA_col (u : Fin L.n → AE F E) (j : Fin d.n) : uA L u j L.i₀ = if j = L.i₀ then 1 else 0 := by
  simp [uA, Matrix.add_apply, Matrix.sum_apply, Matrix.one_apply, fun k => (ComplexParameterFamilyContinuity.em_ne L k)]

theorem uA_mul_aB (u : Fin L.n → AE F E) (δ : E) (a : AF F) : uA L u * aB L δ a = aB L δ a := by
  simp only [uA, aB, add_mul, one_mul, Finset.sum_mul]
  rw [Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (ComplexParameterFamilyContinuity.em_ne L j) _, add_zero]

theorem aB_mul_D (u : Fin L.n → AE F E) (δ : E) (a : AF F) : aB L δ a * (uA L u)ᵀ.map (cA σ) = aB L δ a := by
  ext i j
  simp only [aB, Matrix.mul_apply, Matrix.single_apply, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hi : L.i₀ = i
  · subst hi
    by_cases hj : j = L.i₀
    · subst hj; simp [uA_col]
    · simp [uA_col, hj, Ne.symm hj]
  · simp [hi]

theorem aB_add (δ : E) (a a' : AF F) : aB L δ (a + a') = aB L δ a + aB L δ a' := by
  simp only [aB, add_smul, Matrix.single_add]

theorem sB_add (b b' : Fin L.n → AE F E) : sB R L (b + b') = sB R L b + sB R L b' := by
  simp only [sB, Pi.add_apply, map_add (f := _), mul_add, neg_add, Matrix.single_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by abel

def padB (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ k, ∑ l, Matrix.single (L.em k) (L.em l) (β k l)

theorem padB_apply_i0_eq_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (j : Fin d.n) : padB L β L.i₀ j = 0 := by
  simp [padB, Matrix.sum_apply, fun k => ComplexParameterFamilyContinuity.em_ne L k]

theorem pad_block_col_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i : Fin d.n) : padB L β i L.i₀ = 0 := by
  simp [padB, Matrix.sum_apply, fun k => ComplexParameterFamilyContinuity.em_ne L k]

theorem padB_em (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (k l : Fin L.n) : padB L β (L.em k) (L.em l) = β k l := by
  simp [padB, Matrix.sum_apply, Matrix.single_apply, L.inj.eq_iff, ite_and, Finset.sum_ite_eq']

theorem mem_ratV {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : ∃ x : Fin L.n → E, b = GlobalTheory.ThK.incV F x := by
  let φ : (Fin L.n → E) →+ (Fin L.n → AE F E) :=
    AddMonoidHom.compLeft (inclR (F := F) (E := E) (AF F)).toAddMonoidHom (Fin L.n)
  have hle : L.ratV ≤ φ.range := (AddSubgroup.closure_le _).2 (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
  obtain ⟨x, hx⟩ := hle hb
  exact ⟨x, hx.symm⟩

theorem inclR_smul (t : F) (e : E) :
    inclR (F := F) (AF F) (t • e) = algebraMap F (AF F) t • inclR (F := F) (AF F) e := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (t • e) =
    algebraMap F (AF F) t • (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) e
  rw [map_smul, algebraMap_smul]

variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem inFrame_uM' (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (uA L u) 0 0 ((uA L (-u))ᵀ.map (cA σ)) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, lr_of ha (uA_mul_neg L u)]

theorem inFrame_jn (h : Hyp L nb uM nb' w₁ cM δ) (β : nA σ L.Y L.b) :
    inFrame d.b (L.j (nb' β)) = Matrix.fromBlocks 1 (padB L β.1) 0 1 := by
  have hin : ∀ a b, inFrame d.b (L.j (nb' β)) (Sum.map L.em L.em a) (Sum.map L.em L.em b) = inFrame L.b (nb' β) a b :=
    fun a b => congrFun (congrFun (L.j_in (nb' β)) a) b
  ext r c
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.idx2 L r with rfl | rfl | ⟨a, rfl⟩
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply, padB_apply_i0_eq_zero]
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply]
  · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.idx2 L c with rfl | rfl | ⟨b, rfl⟩
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, ComplexParameterFamilyContinuity.em_ne]
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, pad_block_col_zero, ComplexParameterFamilyContinuity.em_ne]
    · rw [hin, h.nb' β]
      rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, padB_em, L.inj.eq_iff]

theorem inFrame_centre_matrix (h : Hyp L nb uM nb' w₁ cM δ) (a : AF F) :
    inFrame d.b (cM (0, a)) = Matrix.fromBlocks 1 (aB L δ a) 0 1 := by
  rw [inFrame_cM h]
  simp [uA_zero, Matrix.transpose_one]

theorem sM_add (b b' : Fin L.n → AE F E) : sM R L (b + b') = sM R L b * sM R L b' := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, inFrame_sM', inFrame_sM', inFrame_sM', sB_add]
  exact (kfour.nM_mul _ _).symm

theorem cM_split (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : cM (u, a) = uM u * cM (0, a) := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, inFrame_cM h, inFrame_uM' h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply]
  simp [uA_mul_aB]

theorem cM_comm (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : uM u * cM (0, a) = cM (0, a) * uM u := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, KAway.inFrame_mul, inFrame_uM' h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [uA_mul_aB, aB_mul_D]

theorem centre_matrix_add (h : Hyp L nb uM nb' w₁ cM δ) (a a' : AF F) : cM (0, a + a') = cM (0, a) * cM (0, a') := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, inFrame_centre_matrix h, inFrame_centre_matrix h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply, aB_add]
  simp [add_comm]

theorem siegel_centre_commute (h : Hyp L nb uM nb' w₁ cM δ) (b : Fin L.n → AE F E) (a : AF F) : sM R L b * cM (0, a) = cM (0, a) * sM R L b := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, KAway.inFrame_mul, inFrame_centre_matrix h, inFrame_sM', bMat, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem nb_split (h : Hyp L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) :
    nb β = L.j (nb' (C4.prj L β)) * (sM R L (pb L β) * cM (0, pa L δ β)) := by
  have hc : β.1ᵀ = -((((R.ε : ℤ) : AE F E)) • β.1.map (cA σ)) := (kfour.mem_nA_iff (sig2 d) R.hε β.1).1 β.2
  have hcij : ∀ i j, β.1 j i = -(((R.ε : ℤ) : AE F E) * cA σ (β.1 i j)) := fun i j => by
    have := congrFun (congrFun hc i) j
    simpa using this
  have e2 := eps_mul R
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, KAway.inFrame_mul, inFrame_jn h, inFrame_sM', inFrame_centre_matrix h, h.nb β, bMat,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  rcases idx L i with rfl | ⟨k, rfl⟩ <;> rcases idx L j with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.add_apply, sB_i0i0, sB_i0em, siegel_block_embedded_row, sB_emem, padB_apply_i0_eq_zero, pad_block_col_zero, padB_em, aB,
      Matrix.single_apply, C4.prj_val, Matrix.submatrix_apply, pb, pa, eA_eq, fun k => (ComplexParameterFamilyContinuity.em_ne L k).symm, and_self, and_false, false_and, if_true, if_false, add_zero, zero_add]
  · have hy : cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * β.1 L.i₀ L.i₀ := by
      have e := hcij L.i₀ L.i₀
      calc cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * -(((R.ε : ℤ) : AE F E) * cA σ (β.1 L.i₀ L.i₀)) := by
            rw [neg_mul_neg, ← mul_assoc, e2, one_mul]
        _ = _ := by rw [← e]
    exact (eig h _ hy).symm
  · exact hcij _ _

theorem sM_rat {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : sM R L b ∈ rat2 σ d.Y := by
  obtain ⟨x, rfl⟩ := mem_ratV L hb
  have hc (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
    show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
    simp
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (x j) +
    Matrix.single (L.em j) L.i₀ (-(((R.ε : ℤ) : E) * σ (x j))))) 0 1) ?_
  rw [inFrame_sM']
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>

    simp [bMat, incM, Matrix.map_apply, sB, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
    map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), GlobalTheory.ThK.incV, hc, eA, map_neg, map_mul,
    map_intCast]

theorem cM_rat (h : Hyp L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨x, rfl⟩ := mem_ratV L hu
  obtain ⟨t, rfl⟩ := ha
  have hc (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
    show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
    simp
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (x j))
    (Matrix.single L.i₀ L.i₀ (t • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-(x j)))ᵀ.map σ)) ?_
  rw [inFrame_cM h]
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>

    simp [uA, aB, incM, Matrix.map_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
    Matrix.transpose_apply, map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), apply_ite (cA σ), apply_ite (⇑σ), GlobalTheory.ThK.incV,
    hc, map_neg, inclR_smul]

theorem fix_sM (b : Fin L.n → AE F E) (k) :
    inFrame d.b (sM R L b) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [inFrame_sM']
  rcases k with k | k <;> simp [bMat, Matrix.one_apply]

theorem fix_cM (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (k) :
    inFrame d.b (cM c) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [inFrame_cM h]
  rcases k with k | k <;> simp [uA_col, Matrix.one_apply]

theorem fix_nb (h : Hyp L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) (k) :
    inFrame d.b (nb β) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [h.nb β]
  rcases k with k | k <;> simp [Matrix.one_apply]

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinNormSumRationalInvariant =====
