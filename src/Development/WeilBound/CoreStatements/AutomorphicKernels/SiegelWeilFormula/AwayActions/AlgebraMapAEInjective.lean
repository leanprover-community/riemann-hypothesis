module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SumIdemMul
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SigmaSigma
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem algebraMap_AE_injective : Function.Injective (algebraMap (AF F) (AE F E)) := by
  exact FaithfulSMul.algebraMap_injective (AF F) (AE F E)

instance isIntegral_AE : Algebra.IsIntegral (AF F) (AE F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  infer_instance

theorem span_top' (hcm : IsCMExt F E σ) {n : ℕ} (ε : ℤ) (hε : ε * ε = 1)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : IsUnit X.det) :
    Ideal.span {a : AF F | ∃ g, IsEH σ ε g ∧ algebraMap (AF F) (AE F E) a =
      (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det * cA σ (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det} = ⊤ := by
  by_contra hI
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  haveI := hm
  have hker : RingHom.ker (algebraMap (AF F) (AE F E)) ≤ m := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := algebraMap_AE_injective (by rw [hx, map_zero])
    rw [hx0]
    exact m.zero_mem
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  haveI := hQ
  letI : Field (AE F E ⧸ Q) := Ideal.Quotient.field Q
  obtain ⟨g, hg, h1, h2⟩ := exists_point hcm ε hε X hX (Ideal.Quotient.mk Q)
  obtain ⟨a, ha⟩ := nrm_exists hcm (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det
  have haI : a ∈ m := hIm (Ideal.subset_span ⟨g, hg, ha⟩)
  rw [← hQm] at haI
  have h0 : Ideal.Quotient.mk Q (algebraMap (AF F) (AE F E) a) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 haI
  rw [ha, map_mul] at h0
  exact mul_ne_zero h1 h2 h0

end PositivityTheory.SiegelWeilFormula.KAway

end
