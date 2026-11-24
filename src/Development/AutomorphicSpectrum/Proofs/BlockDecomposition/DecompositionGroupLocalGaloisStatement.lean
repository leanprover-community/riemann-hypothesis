module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.MaximalUnramified
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGalois
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import GroundTheory.ProfiniteCohomology.ProcyclicDefs

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

theorem _root_.GlobalTheory.T.decomposition_group_local_galois : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  first | exact @GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | exact GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | (intros; apply GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one <;> assumption)
