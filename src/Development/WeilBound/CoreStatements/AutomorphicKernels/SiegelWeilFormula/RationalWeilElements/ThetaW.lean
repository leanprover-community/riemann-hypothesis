module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaSumRationalInvariant
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.TW.ThetaWPf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isW_rat (d : SD σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) : w ∈ rat2 σ d.Y := by
  refine PositivityTheory.SiegelWeilFormula.kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
  rw [(hw : inFrame d.b w = _)]
  ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp

theorem thetaW : ThetaW := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun ε w hw Φ hΦ => ?_, GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ⟩
  exact ⟨d.ok.dbl.weil.2.1.pres w Φ hΦ, PositivityTheory.SiegelWeilFormula.Tauto.theta_sum_rational_invariant d w (isW_rat d hw) Φ hΦ⟩

end PositivityTheory.SiegelWeilFormula.TW.ThetaWPf

end
