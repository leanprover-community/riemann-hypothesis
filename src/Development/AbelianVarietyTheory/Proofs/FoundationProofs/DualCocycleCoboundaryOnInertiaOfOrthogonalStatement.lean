module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnInertiaOfOrthogonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualCocycle_coboundary_on_inertia_of_orthogonal : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  first | exact @GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | exact GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | (intros; apply GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | exact GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | (intros; apply GlobalTheory.Ord2.GwIneq.cob_of_perp_transport <;> assumption)
