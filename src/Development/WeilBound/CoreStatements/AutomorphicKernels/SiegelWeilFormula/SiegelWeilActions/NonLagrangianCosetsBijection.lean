module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.GeometricRayBounds
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InFrameW1EmSEqOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
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
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses, Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.PaddedMatrixIdentity.Conjpar, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DiscFubiniVolume, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijectionRank, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijection

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Act.C6

end PositivityTheory.SiegelWeilFormula.Act.C6

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.PaddedMatrixIdentity.Conjpar =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.PaddedMatrixIdentity.Conjpar", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.GeometricRayBounds\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem padded_matrix_mul_submatrix (A : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (padM L A * N).submatrix (emS L) (emS L) = A * N.submatrix (emS L) (emS L) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (emS L) (emS_inj L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, emS L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [padM_out_col L A _ hl', Matrix.one_apply_ne, zero_mul]
    rintro rfl
    exact hl' ⟨a, rfl⟩
  · intro b
    rw [padM_emS]

theorem mul_padded_matrix_submatrix (B : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (N * padM L B).submatrix (emS L) (emS L) = N.submatrix (emS L) (emS L) * B := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (emS L) (emS_inj L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, emS L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [padM_out_row L B hl', Matrix.one_apply_ne, mul_zero]
    rintro rfl
    exact hl' ⟨c, rfl⟩
  · intro b
    rw [padM_emS]

theorem parabolic_conj_weyl_crossing (h : Hyp L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈ rat2 σ L.Y) (c : Cr L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : Cr L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) := by
  have hx : (L.j p')⁻¹ * cM c.1 * L.j p' ∈ rat2 σ d.Y :=
    mul_mem (mul_mem (inv_mem (j_rat L hpr)) (cM_rat' h c.2.1 c.2.2)) (j_rat L hpr)
  have hf : Fix L ((L.j p')⁻¹ * cM c.1 * L.j p') :=
    fix_mul (fix_mul (fix_inv (fix_j p')) (fix_cM' h c.1)) (fix_j p')
  obtain ⟨s, c₂, γ', hs, hsP, -, hγ', hx'⟩ := stab_dec h hx hf
  have hsub : (inFrame d.b ((L.j p')⁻¹ * cM c.1 * L.j p')).submatrix (emS L) (emS L) = 1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_inv, inFrame_j, inFrame_j,
      mul_padded_matrix_submatrix, padded_matrix_mul_submatrix, emS_cM h, Matrix.mul_one, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hγ1 : γ' = 1 := kunf.inFrame_injective L.b (by rw [hγ', hsub, GlobalTheory.EisBL.DoubledParabolic.inFrame_one])
  rw [hγ1, map_one, mul_one] at hx'
  refine ⟨L.j p' * (w₁ * s * w₁⁻¹), mul_mem (j_par L hp) hsP,
    mul_mem (j_rat L hpr) (mul_mem (mul_mem h.wr hs) (inv_mem h.wr)), c₂, ?_⟩
  have hw := w1_mul_j_comm h p'
  calc w₁ * (cM c.1 * L.j p') = w₁ * L.j p' * ((L.j p')⁻¹ * cM c.1 * L.j p') := by group
    _ = L.j p' * w₁ * (s * cM c₂.1) := by rw [hw, hx']
    _ = L.j p' * (w₁ * s * w₁⁻¹) * (w₁ * cM c₂.1) := by group

end PositivityTheory.SiegelWeilFormula.Act.C6

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.PaddedMatrixIdentity.Conjpar =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DiscFubiniVolume =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DiscFubiniVolume", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InFrameW1EmSEqOne\npublic import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.PaddedMatrixIdentity.Conjpar\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Act.C6

end PositivityTheory.SiegelWeilFormula.Act.C6

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DiscFubiniVolume =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijectionRank =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijectionRank", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DiscFubiniVolume\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.GeometricRayBounds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem non_lagrangian_cosets_bijection_rank (h : Hyp L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : Cs L.sd, Cr L) ≃ {q : Cs d // ¬ LagrangianCondition L (rep q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      rep (e x).1 = p * (w₁ * (cM x.2.1 * L.j (rep x.1))) := by
  have hg : ∀ x : (Σ _ : Cs L.sd, Cr L), w₁ * (cM x.2.1 * L.j (rep x.1)) ∈ rat2 σ d.Y := fun x =>
    (rat2 σ d.Y).mul_mem h.wr ((rat2 σ d.Y).mul_mem (cM_rat' h x.2.2.1 x.2.2.2) (j_rat L (rep_mem L.sd x.1)))
  have hfix : ∀ x : (Σ _ : Cs L.sd, Cr L), Fix L (cM x.2.1 * L.j (rep x.1)) := fun x => fix_mul (fix_cM' h _) (fix_j _)
  let Fm : (Σ _ : Cs L.sd, Cr L) → {q : Cs d // ¬ LagrangianCondition L (rep q)} := fun x =>
    ⟨Quotient.mk _ ⟨_, hg x⟩, by
      obtain ⟨p, hp, -, e⟩ := out_mk d ⟨_, hg x⟩
      rw [e, lagrangian_condition_parabolic_iff hp]
      exact not_lagrangian_w1_mul h (hfix x)⟩
  have hinj : Function.Injective Fm := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ hE
    have hE' : (Quotient.mk _ ⟨_, hg ⟨q₁, c₁⟩⟩ : Cs d) = Quotient.mk _ ⟨_, hg ⟨q₂, c₂⟩⟩ := congrArg Subtype.val hE
    rw [mk_eq_mk] at hE'
    set g₁ := w₁ * (cM c₁.1 * L.j (rep q₁))
    set g₂ := w₁ * (cM c₂.1 * L.j (rep q₂))
    have e : (g₂ * g₁⁻¹) * (w₁ * (cM c₁.1 * L.j (rep q₁))) = w₁ * (cM c₂.1 * L.j (rep q₂)) := by
      simp only [g₁, g₂]; group
    have hpr : g₂ * g₁⁻¹ ∈ rat2 σ d.Y := (rat2 σ d.Y).mul_mem (hg ⟨q₂, c₂⟩) ((rat2 σ d.Y).inv_mem (hg ⟨q₁, c₁⟩))
    obtain ⟨hP, hc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.inj_core h hE' hpr (rep_mem L.sd q₁) (rep_mem L.sd q₂) e
    have hq : q₁ = q₂ := by
      rw [← mk_rep L.sd q₁, ← mk_rep L.sd q₂, mk_eq_mk]
      exact hP
    subst hq
    rw [hc rfl]
  have hsurj : Function.Surjective Fm := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hp, hpr, hfx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.normalize h (rep_mem d q) hq
    have hr : w₁⁻¹ * (p * rep q) ∈ rat2 σ d.Y :=
      (rat2 σ d.Y).mul_mem ((rat2 σ d.Y).inv_mem h.wr) ((rat2 σ d.Y).mul_mem hpr (rep_mem d q))
    obtain ⟨s, c, γ', hsr, hW, hγ', -, hx⟩ := stab_dec h hr hfx
    obtain ⟨p', hp', hp'r, he'⟩ := out_mk L.sd ⟨γ', hγ'⟩
    obtain ⟨p₂, hp₂, hp₂r, c₂, hc₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.parabolic_conj_weyl_crossing h ((par2 σ L.Y).inv_mem hp') ((rat2 σ L.Y).inv_mem hp'r) c
    refine ⟨⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩, Subtype.ext ?_⟩
    show (Quotient.mk _ ⟨_, hg ⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩⟩ : Cs d) = q
    conv_rhs => rw [← mk_rep d q]
    rw [mk_eq_mk]
    have hγ'' : γ' = p'⁻¹ * rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd) := by rw [he']; group
    have key : p * rep q = (w₁ * s * w₁⁻¹) * p₂ * (w₁ * (cM c₂.1 * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd)))) := by
      have h1 : p * rep q = w₁ * (s * (cM c.1 * L.j γ')) := by rw [← hx]; group
      rw [h1]
      conv_lhs => rw [hγ'', map_mul]
      have h2 : w₁ * (s * (cM c.1 * (L.j p'⁻¹ * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd))))) =
          (w₁ * s * w₁⁻¹) * ((w₁ * (cM c.1 * L.j p'⁻¹)) * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd))) := by group
      rw [h2, hc₂]
      group
    have : rep q * (w₁ * (cM c₂.1 * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd))))⁻¹ = p⁻¹ * ((w₁ * s * w₁⁻¹) * p₂) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, key]; group
    rw [this]
    exact (par2 σ d.Y).mul_mem ((par2 σ d.Y).inv_mem hp) ((par2 σ d.Y).mul_mem hW hp₂)
  refine ⟨Equiv.ofBijective Fm ⟨hinj, hsurj⟩, fun x => ?_⟩
  obtain ⟨p, hp, hpr, e⟩ := out_mk d ⟨_, hg x⟩
  exact ⟨p, hp, hpr, e⟩

end PositivityTheory.SiegelWeilFormula.Act.C6

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijectionRank =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijection =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijection", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijectionRank\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
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

variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem non_lagrangian_cosets_bijection (h : Hyp L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : Cs L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr L) ≃ {q : Cs d // ¬ LagrangianCondition L (rep q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      rep (e x).1 = p * (w₁ * (cM x.2.1 * L.j (rep x.1))) := by
  exact C6.non_lagrangian_cosets_bijection_rank ⟨h.nb, h.uM, h.nb', h.wr, h.wf, h.cf, h.δ0⟩

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijection =====
