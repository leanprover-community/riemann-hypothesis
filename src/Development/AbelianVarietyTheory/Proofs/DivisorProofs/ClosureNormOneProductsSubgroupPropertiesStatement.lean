module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupProperties
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.closure_normOneProducts_h0_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε → (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε), x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε), rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  first | exact @GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | exact GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | (intros; apply GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties <;> assumption)
