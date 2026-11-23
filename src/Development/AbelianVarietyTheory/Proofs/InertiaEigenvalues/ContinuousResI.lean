module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

noncomputable section

namespace GlobalTheory.WeilRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun i => (b i : Ω)
  have : Finite S := (Set.finite_range _).to_subtype
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff E' Ω _).mpr ⟨IntermediateField.adjoin E' S,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun σ hσ => hLU ?_⟩
  have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
  have hlin : (AlgEquiv.restrictScalarsHom E σ).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => hσ' _ (IntermediateField.subset_adjoin E' S ⟨i, rfl⟩)
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end GlobalTheory.WeilRes

end
