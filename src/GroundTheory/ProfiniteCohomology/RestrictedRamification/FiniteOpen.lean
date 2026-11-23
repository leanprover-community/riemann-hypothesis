module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

universe u

section Places

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

theorem placesOver_finite {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) :
    (placesOver S : Set (HeightOneSpectrum (𝓞 L))).Finite := by
  have hfin : ∀ v ∈ S, {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.LiesOver v.asIdeal}.Finite := by
    intro v _
    have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)
    refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
      fun a _ b _ hab => HeightOneSpectrum.ext hab).subset ?_
    intro w hw
    exact ⟨w.isPrime, hw⟩
  refine (hS.biUnion hfin).subset ?_
  rintro w ⟨v, hv, hwv⟩
  exact Set.mem_biUnion hv hwv


omit [NumberField F] [NumberField L] in
theorem mem_placesOver_of_natCast_mem {S : Set (HeightOneSpectrum (𝓞 F))} {n : ℕ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    {w : HeightOneSpectrum (𝓞 L)} (hw : ((n : ℕ) : 𝓞 L) ∈ w.asIdeal) : w ∈ placesOver S := by
  refine (mem_placesOver_iff (F := F) (L := L)).2 (hn _ ?_)
  change ((n : ℕ) : 𝓞 F) ∈ Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) w.asIdeal
  rw [Ideal.mem_comap, map_natCast (algebraMap (𝓞 F) (𝓞 L))]
  exact hw


omit [NumberField F] [NumberField L] in
theorem natCast_not_mem_of_not_mem_placesOver {S : Set (HeightOneSpectrum (𝓞 F))} {n : ℕ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) :
    ∀ w ∉ (placesOver S : Set (HeightOneSpectrum (𝓞 L))), ((n : ℕ) : 𝓞 L) ∉ w.asIdeal :=
  fun _ hw hmem => hw (mem_placesOver_of_natCast_mem hn hmem)

end Places

section OpenSubgroups

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

theorem mem_gsOpenSubgroup_iff_of_image {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (T : Set (maxUnramifiedOutside K.1 ℚ̄ S)) (hT : ∀ x : L.1, gsEmbedding hL x ∈ T)
    (hT' : ∀ y ∈ T, ∃ x : L.1, gsEmbedding hL x = y) (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    σ ∈ gsOpenSubgroup S hL ↔ ∀ y ∈ T, σ y = y := by
  rw [mem_gsOpenSubgroup_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hT' y hy
    exact h x
  · intro h x
    exact h _ (hT x)

theorem exists_gsOpenSubgroup_eq (V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    ∃ (L : FiniteSubfield) (_ : Fact (K ≤ L))
      (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      gsOpenSubgroup S hL = V := by
  let KS := maxUnramifiedOutside K.1 ℚ̄ S
  let H : ClosedSubgroup Gal(KS/K.1) := ⟨(V : Subgroup Gal(KS/K.1)), V.isClosed⟩
  let E : IntermediateField K.1 KS := IntermediateField.fixedField (H : Subgroup Gal(KS/K.1))
  have hEV : E.fixingSubgroup = (V : Subgroup Gal(KS/K.1)) :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have hEfin : FiniteDimensional K.1 E := by
    rw [← InfiniteGalois.isOpen_iff_finite E, hEV]
    exact V.isOpen
  let E' : IntermediateField K.1 ℚ̄ := E.map KS.val
  have hE'fin : FiniteDimensional K.1 E' :=
    LinearEquiv.finiteDimensional (E.equivMap KS.val).toLinearEquiv
  have hE'Q₀ : FiniteDimensional ℚ E' := FiniteDimensional.trans ℚ K.1 E'
  have hE'Q : FiniteDimensional ℚ (E'.restrictScalars ℚ) := hE'Q₀
  have hKL : K ≤ ⟨E'.restrictScalars ℚ, hE'Q⟩ := by
    intro x hx
    change x ∈ E'
    have : algebraMap K.1 ℚ̄ ⟨x, hx⟩ ∈ E' := E'.algebraMap_mem _
    exact this
  have hKS : ∀ x : (⟨E'.restrictScalars ℚ, hE'Q⟩ : FiniteSubfield).1,
      algebraMap (⟨E'.restrictScalars ℚ, hE'Q⟩ : FiniteSubfield).1 ℚ̄ x ∈ KS := by
    intro x
    obtain ⟨y, -, hy⟩ := (x.2 : (x : ℚ̄) ∈ E')
    change (x : ℚ̄) ∈ KS
    rw [← hy]
    exact y.2
  have : Fact (K ≤ ⟨E'.restrictScalars ℚ, hE'Q⟩) := ⟨hKL⟩
  refine ⟨⟨E'.restrictScalars ℚ, hE'Q⟩, inferInstance, hKS, ?_⟩
  ext σ
  rw [mem_gsOpenSubgroup_iff_of_image K S hKS (E : Set KS)]
  · change _ ↔ σ ∈ (V : Subgroup Gal(KS/K.1))
    rw [← hEV, IntermediateField.mem_fixingSubgroup_iff]
    rfl
  · intro x
    obtain ⟨y, hy, hyx⟩ := (x.2 : (x : ℚ̄) ∈ E')
    have hy' : y ∈ (E : Set KS) := hy
    convert hy' using 1
    apply Subtype.ext
    exact hyx.symm
  · intro y hy
    exact ⟨⟨(y : ℚ̄), ⟨y, hy, rfl⟩⟩, Subtype.ext rfl⟩

end OpenSubgroups

end

end GroundTheory.ProfCoh
