module

public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import Mathlib.FieldTheory.KrullTopology
public import GroundTheory.ProfiniteCohomology.ColimitUnion
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.AdeleBaseChange

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev ideleRep : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) (IdeleGroup L)

noncomputable def sIdelesSubmodule (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Submodule ℤ (ideleRep K L) :=
  (Subgroup.toAddSubgroup (sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))))).toIntSubmodule

omit [NumberField K] in
variable {K L} in
theorem mem_sIdelesSubmodule {S : Finset (HeightOneSpectrum (𝓞 K))} {a : ideleRep K L} :
    a ∈ sIdelesSubmodule K L S ↔
      a.toMul ∈ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  Iff.rfl


omit [NumberField K] in
theorem sIdelesSubmodule_mono : Monotone (sIdelesSubmodule K L) := fun _ _ h _ ha =>
  sIdeles_mono (placesAbove_mono (Finset.coe_subset.2 h)) ha


omit [NumberField K] in
theorem sIdelesSubmodule_stable (S : Finset (HeightOneSpectrum (𝓞 K))) (g : Gal(L/K)) :
    sIdelesSubmodule K L S ≤ (sIdelesSubmodule K L S).comap ((ideleRep K L).ρ g) := fun _ ha =>
  smul_mem_sIdeles_placesAbove _ g ha


omit [NumberField K] in
theorem exists_mem_sIdelesSubmodule (a : ideleRep K L) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), a ∈ sIdelesSubmodule K L S := by
  have hfin : (below K '' {w : HeightOneSpectrum (𝓞 L) | ord w a.toMul ≠ 0}).Finite :=
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero a.toMul)).image _
  refine ⟨hfin.toFinset, fun w hw => ?_⟩
  by_contra h
  exact hw (by
    rw [mem_placesAbove, Set.Finite.coe_toFinset]
    exact ⟨w, h, rfl⟩)

variable [IsGalois K L]

theorem exists_sIdeles_cohomology_eq (n : ℕ) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (x : cohomology (ideleRep K L) n) :
    ∃ S, S₀ ⊆ S ∧ ∃ y : cohomology ((ideleRep K L).subrepresentation (sIdelesSubmodule K L S)
        (sIdelesSubmodule_stable K L S)) n,
      (cohomologyMap (Rep.subtype (ideleRep K L) (sIdelesSubmodule K L S)
        (sIdelesSubmodule_stable K L S)) n).hom y = x := by
  classical
  obtain ⟨S, y, hy⟩ := exists_cohomologyMap_subtype_eq (ideleRep K L) (sIdelesSubmodule K L)
    (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) (exists_mem_sIdelesSubmodule K L) n x
  have h : S ≤ S ∪ S₀ := Finset.subset_union_left
  refine ⟨S ∪ S₀, Finset.subset_union_right, (cohomologyMap (subrepInclusion (ideleRep K L)
    (sIdelesSubmodule K L) (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) h) n).hom y,
    ?_⟩
  have e := subrepInclusion_comp_subtype (ideleRep K L) (sIdelesSubmodule K L)
    (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) h
  rw [← hy, ← ModuleCat.comp_apply, ← cohomologyMap_comp, e]

end GroundTheory.ProfCoh
