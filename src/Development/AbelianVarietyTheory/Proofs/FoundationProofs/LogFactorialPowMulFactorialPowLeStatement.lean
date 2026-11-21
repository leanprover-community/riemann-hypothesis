import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogFactorialPowMulFactorialPowLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import BuildAid.ForwardExisting

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' : ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R → Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  atlas_forward_decl GlobalTheory.log_factorial_pow_mul_factorial_pow_le
