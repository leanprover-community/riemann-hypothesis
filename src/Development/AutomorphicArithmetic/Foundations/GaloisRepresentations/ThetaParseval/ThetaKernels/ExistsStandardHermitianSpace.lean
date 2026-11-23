module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsHermUnitSpcK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFrameConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStdEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen
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
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_standard_hermitian_space {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Y₀ : Spc F E n) (b₀ : GL (Fin n ⊕ Fin n) E) (K₀ : Subgroup (G2 σ Y₀)) (a₀ : G2 σ Y₀ → ℝ),
      IsFrame2 σ Y₀ b₀ ∧ b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n 1 ∧
      IsStdK (σ := σ) (Y := Y₀) B b₀ K₀ ∧ IsHgt K₀ a₀ := by
  obtain ⟨b, K, a, hb, hK, ha, -, -⟩ :=
    _root_.GlobalTheory.ThK.Dbl.stdEx_of_k _root_.GlobalTheory.ThK.Dbl.frameConj_k _root_.GlobalTheory.ThK.Dbl.hgtEx_k F E σ B n (UnitHermitianSpace.unitSpc F E n) n 0 hB (Or.inl (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n))
  refine ⟨UnitHermitianSpace.unitSpc F E n, b, K, a, hb, ?_, hK, ha⟩
  obtain ⟨ε, hε⟩ := hb.1
  have hc : ∀ z : E, σ (σ z) = z := (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n).herm |> fun _ => by
    intro z
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have h1 := eps_one hn hc (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n).herm hε
  rw [hε, eps_unit h1]
  simp [Ald.jeps]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
