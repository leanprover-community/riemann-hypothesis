module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FirstOrbitParabolicLeft
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.LagrangianConditionParabolicMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace N
theorem fix_of_col_k {w x : d.G}
    (hc : ∀ r, inFrame d.b x r (Sum.inl L.i₀) = inFrame d.b w r (Sum.inl L.i₀)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w⁻¹ * x) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp_rw [hc]
  rw [← Matrix.mul_apply, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
theorem weyl_base_column (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧ ∀ r, inFrame d.b w₁ r (Sum.inl L.i₀) =
    inclR (F := F) (AF F) ((Pi.single (Sum.inr L.i₀) b₀ : Fin d.n ⊕ Fin d.n → E) r) := by
  obtain ⟨a, b, -, hb, hw⟩ := h.wf
  refine ⟨b, hb, fun r => ?_⟩
  rw [hw]
  rcases r with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
theorem normalize_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w₁⁻¹ * (p * γ)) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  have hform := Bq.form_E hε γ hG0
  obtain ⟨b₀, hb₀, hw1⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.weyl_base_column h
  have hy : (fun k => G0 (Sum.inr k) (Sum.inl L.i₀)) ≠ 0 := by
    intro h0
    apply hn
    intro i
    rw [hG0]
    show inclR (F := F) (AF F) (G0 (Sum.inr i) (Sum.inl L.i₀)) = 0
    rw [congrFun h0 i, Pi.zero_apply, map_zero]
  obtain ⟨A, β0, hβ, hcol⟩ := exists_E L.i₀ hσ ε hform hb₀ hy
  obtain ⟨pm, hpmr, hpm⟩ := Afc.levi_ex hσ d.ok.frame A
  have hpmP : pm ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pm).2 (by rw [hpm, Matrix.toBlocks_fromBlocks₂₁])
  have hβA : incM F β0 ∈ nA σ d.Y d.b := (kfour.mem_nA_iff hσ hε _).2 (nCond_of_E ε hβ)
  set pn := nb ⟨incM F β0, hβA⟩ with hpn_def
  have hpn : inFrame d.b pn = Matrix.fromBlocks 1 (incM F β0) 0 1 := h.nb _
  have hpnP : pn ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pn).2 (by rw [hpn, Matrix.toBlocks_fromBlocks₂₁])
  have hpnr : pn ∈ rat2 σ d.Y :=
    kunf.rat_of_inFrame (M := Matrix.fromBlocks 1 β0 0 1) (by rw [hpn, kfour.incM_nM]; rfl)
  refine ⟨pn * pm, mul_mem hpnP hpmP, mul_mem hpnr hpmr, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.fix_of_col_k fun r => ?_⟩
  have hF : inFrame d.b (pn * pm * γ) =
      incM F (Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hpn, hpm, hG0, kfour.incM_mul', kfour.incM_mul',
      kfour.incM_nM, Afc.incM_fromBlocks, kfour.incM_zero]
    rfl
  rw [hF, hw1 r]
  show inclR (F := F) (AF F) _ = _
  rw [hcol r]
end N
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
