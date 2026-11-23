module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylBase
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.DetWeylBlockNeZero
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem detY_k : d.Y.J.det ≠ 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  intro h0
  have hd : (dbl d.Y.J).det = 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₁₂, h0, zero_mul]
  have h := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, hd, mul_zero, zero_mul] at h
  exact det_weyl_block_ne_zero ε h.symm
theorem signY_k : ∃ ε : ℤˣ, ∀ i j, σ (d.Y.J j i) = ((ε : ℤ) : E) * d.Y.J i j := by
  rcases d.ok.sign with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨-1, fun i j => by rw [h]; simp⟩
  · exact ⟨1, fun i j => by rw [h]; simp⟩
theorem exists_l_ne_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : ∃ φ ∈ schA F d.κ, d.l φ ≠ 0 := by
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have hne : d.T φz ≠ 0 := fun h => hφz0 (by rw [(hT F E σ d).2.2 φz hφz h]; rfl)
  obtain ⟨X, hX⟩ : ∃ X, d.T φz X ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact ⟨_, GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.tweyl.std_k d) _ φz hφz, hX⟩
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
