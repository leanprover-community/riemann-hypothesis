module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicCompletionCongruenceSubgroupsOpenCompactSmal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

theorem _root_.GlobalTheory.T.adicCompletion_congruenceSubgroups_open_compact_small : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → (l : 𝓞 E) ∈ w.asIdeal → (∀ m : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ∧ IsCompact (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E)))) ∧ ∀ N ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), ∀ᶠ m : ℕ in Filter.atTop, (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N := by
  first | exact @GlobalTheory.CongOpenSmall.congruence_open_compact_small | exact GlobalTheory.CongOpenSmall.congruence_open_compact_small | (intros; apply GlobalTheory.CongOpenSmall.congruence_open_compact_small; all_goals assumption)
