module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FrameSignEqInvolutionScalar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaEps
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have s := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε
  have s' := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k L.sd ε' hε'
  refine ⟨ε, hε, ?_⟩
  suffices e : ε' = ε by rw [← e]; exact hε'
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · rw [s.1 hY, s'.1 hY']
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · rw [s.2 hY, s'.2 hY']
end PositivityTheory.SiegelWeilFormula.Avac
end
end
