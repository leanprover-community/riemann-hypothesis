module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPairStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleModelDegreeStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XCkFlagSum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
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

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.CkFlagSum

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B B' : ChartBundle O (mseg x) N V), SameGeneric O x B B' → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ), IsFlagFrame x B w b → IsFlagFrame x B' w' b' → (∀ i j : Fin N, i < j → w.repr (w' i) j = 0) → ∀ A A' : Fin N → ChartBundle O (mseg x) 1 Ω, (∀ i, IsLine O x 1 (b i) (A i).lat ∧ IsLine O x (w.repr (w' i) i) (b' i) (A' i).lat) → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N B B' k L Q = ∑ i, ck O x d 1 (A i) (A' i) k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM N V _ _ B B' hS w w' b b' hF hF' hw A A' hA k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hK, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  have hW' : GroundTheory.Heights₂.Heights.NumbersDVR.IsModelOver (pointIdeal O x) d := hW
  obtain ⟨hG, f, g, hP⟩ :=
    GlobalTheory.T.same_generic_flag_comparison O Ω K ι x ϖ hϖ d hW' N V B B' hS w w' b b' hF hF' hw
  have h1 := (GlobalTheory.T.chern_class_on_flag_pair O ϖ hϖ Ω K ι x d hK hW' N V B B' hG w w' b b' f g hP).1 k hk1 hk2
    (psumExpansion N k) (isPairExpansion_psum N k) q L Q hQ
  have h2 : ∀ i, ck O x d 1 (A i) (A' i) k L Q = _ := fun i =>
    (GlobalTheory.T.line_bundle_model_degree O Ω K ι x ϖ hϖ d hM (A i) (A' i) 1 (w.repr (w' i) i) (b i) (b' i)
      (hA i).1 (hA i).2 (f i) (g i) (hP.vertical i)
      (by rw [mul_one, mul_comm]; exact hP.generic i)).2 k hk1 hk2 q L Q hQ
  refine h1.trans ?_
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [PositivityTheory.Xgn.A_ck_flag_sum.pairNum_psum, Finset.mul_sum]

end GlobalTheory.CompanionTheory.Ar.CkFlagSum
