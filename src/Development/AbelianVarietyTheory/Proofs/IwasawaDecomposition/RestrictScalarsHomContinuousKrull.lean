module

public import Mathlib.FieldTheory.KrullTopology
public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

theorem restrictScalarsHom_continuous_krull (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (K : IntermediateField E Ω) :
    Continuous (AlgEquiv.restrictScalarsHom E : G K Ω →* G E Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨L, hL, hLs⟩ := hs
  let b := Module.finBasis E L
  have hint : ∀ i, IsIntegral K ((b i : L) : Ω) := fun i =>
    ((IsIntegral.of_finite E (b i)).map (IsScalarTower.toAlgHom E L Ω)).tower_top
  have hN : ⋂ i, ((IntermediateField.adjoin K {((b i : L) : Ω)}).fixingSubgroup : Set (G K Ω))
      ∈ nhds (1 : G K Ω) := Filter.iInter_mem.mpr fun i => by
    haveI := IntermediateField.adjoin.finiteDimensional (hint i)
    exact (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hN ?_
  intro σ hσ
  apply hLs
  simp only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, σ ((b i : L) : Ω) = ((b i : L) : Ω) := fun i =>
    hσ i _ (IntermediateField.mem_adjoin_simple_self K _)
  obtain ⟨y, rfl⟩ : ∃ y : L, (y : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr y]
  change (AlgEquiv.restrictScalars E σ) _ = _

  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgEquiv.restrictScalars_apply, hb]

end GlobalTheory
