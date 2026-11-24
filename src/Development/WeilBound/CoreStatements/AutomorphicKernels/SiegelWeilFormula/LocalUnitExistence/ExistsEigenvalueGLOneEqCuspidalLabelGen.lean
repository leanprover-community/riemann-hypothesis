module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.UnitHermitianSpace
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt
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
import Mathlib.Tactic.Linter.HaveILetI
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen

-- ===== clump member: Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def StdEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x

theorem stdEx_of (h1 : FrameConj) (h2 : HgtEx) : StdEx := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY
  obtain ⟨⟨K, a, hK, ha, hc, hp⟩, -⟩ := h2 F E σ B n Y r s hB hY
  obtain ⟨b, K₀, p, t, hb, hK₀, hpt, e⟩ := h1 F E σ B n Y r s hB hY K hK
  have h0 : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det t) := by
    rw [← ha.val p t hpt 1 K.one_mem]
    exact hp _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  refine ⟨b, K₀, fun x => absE F E (Matrix.GeneralLinearGroup.det t) * a (x * p⁻¹), hb, hK₀, ⟨fun x => ?_, fun q u hq k hk => ?_⟩,
    continuous_const.mul (hc.comp (continuous_mul_const _)), fun x => mul_pos h0 (hp _)⟩
  · obtain ⟨q, u, hq, k, hk, ex⟩ := ha.iwa (x * p⁻¹)
    exact ⟨q * p, u * t, hq.mul hpt, _, (e k).1 hk, by rw [mul_inv_eq_iff_eq_mul.1 ex]; group⟩
  · have := ha.val _ _ (hq.mul hpt.inv) (p * k * p⁻¹) ((e _).2 (by convert hk using 1; group))
    rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, this, ← NNReal.coe_mul, ← map_mul, mul_comm, ← map_mul,
      inv_mul_cancel_right]

end GlobalTheory.ThK.Dbl

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.UnitHermitianSpace\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt\npublic import Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


omit [NumberField F] [NumberField E] in
theorem eps_one {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {ε : ℤˣ}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : ((ε : ℤ) : E) = 1 := by
  have hD : ((dbl J).map σ)ᵀ = dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]
  set G := bᵀ * dbl J * b.map σ with hG
  have hs : (G.map σ)ᵀ = G := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]
    have e : (⇑σ ∘ ⇑σ) = id := funext hc
    rw [e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose], Matrix.mul_assoc]
  have := congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  rw [hb] at this
  simpa [Matrix.fromBlocks] using this

theorem eps_unit {ε : ℤˣ} (h : ((ε : ℤ) : E) = 1) : ε = 1 := by
  rcases Int.units_eq_one_or ε with e | e
  · exact e
  · exfalso
    rw [e] at h
    have : (2 : E) = 0 := by
      have h' : ((-1 : ℤ) : E) = 1 := by exact_mod_cast h
      push_cast at h'
      linear_combination -h'
    exact two_ne_zero this

theorem exists_eigenvalueGLOne_eq_cuspidalLabel_gen {B : Base F E} (hB : B.IsGood σ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Y₀ : Spc F E n) (b₀ : GL (Fin n ⊕ Fin n) E) (K₀ : Subgroup (G2 σ Y₀)) (a₀ : G2 σ Y₀ → ℝ),
      IsFrame2 σ Y₀ b₀ ∧ b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n 1 ∧
      IsStdK (σ := σ) (Y := Y₀) B b₀ K₀ ∧ IsHgt K₀ a₀ := by
  obtain ⟨b, K, a, hb, hK, ha, -, -⟩ :=
    stdEx_of frameConj hgtEx F E σ B n (UnitHermitianSpace.unitSpc F E n) n 0 hB (Or.inl (UnitHermitianSpace.isHerm_unitSpc hB n))
  refine ⟨UnitHermitianSpace.unitSpc F E n, b, K, a, hb, ?_, hK, ha⟩
  obtain ⟨ε, hε⟩ := hb.1
  have hc : ∀ z : E, σ (σ z) = z := (UnitHermitianSpace.isHerm_unitSpc hB n).herm |> fun _ => by
    intro z
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have h1 := eps_one hn hc (UnitHermitianSpace.isHerm_unitSpc hB n).herm hε
  rw [hε, eps_unit h1]
  simp [Ald.jeps]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen =====
