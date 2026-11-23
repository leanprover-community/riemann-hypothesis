module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.exists_global_uniformizer_residue_representatives : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  first | exact @GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | exact GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | (intros; apply GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives <;> assumption)
