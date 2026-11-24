module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob

theorem finite_not_ine_le_of_isOpen : ∀ (Ω : Type) [Field Ω] (k : Type) [Field k] [NumberField k] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : Subgroup (G k Ω)), IsOpen (N : Set (G k Ω)) →
    {w : HeightOneSpectrum (𝓞 k) | ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ¬ Ine (F := k) A ≤ N}.Finite := by
  intro Ω _ k _ _ _ _ N hN
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff k Ω (N : Set (G k Ω))).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional k L := hL
  refine (GlobalTheory.InertiaAlmostAll.finite_ramified k Ω L).subset ?_
  rintro w ⟨B, hB, h⟩
  exact ⟨B, hB, fun h' => h fun x hx => hLN (h' hx)⟩

end GlobalTheory.DelGlob
