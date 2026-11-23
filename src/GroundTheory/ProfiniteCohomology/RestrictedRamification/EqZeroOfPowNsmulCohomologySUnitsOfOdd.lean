module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighSUnits
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnits
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnitsLocal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecompLadic
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDivisor
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
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

section TwoTorsion

variable {K : FiniteSubfield}

theorem two_nsmul_cohomology_unitsLimitRep {r : ℕ} (hr : 4 ≤ r) (y : cohomology (unitsLimitRep K) r) :
    2 • y = 0 := by
  obtain ⟨ι⟩ := nonempty_localEmbeddings K
  apply (bijective_realLocalization ι hr).1
  rw [map_nsmul, map_zero]
  funext v
  rw [Pi.smul_apply]
  rcases Nat.even_or_odd r with he | ho
  · have hc := natCard_localGaloisCohomology_of_isReal_of_even v.1 v.2 (by omega) he
    rw [← hc]
    exact card_nsmul_eq_zero'
  · have := subsingleton_localGaloisCohomology_of_isReal_of_odd v.1 v.2 ho
    exact Subsingleton.elim _ _

end TwoTorsion

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)


include hℓ hS in
theorem eq_zero_of_pow_nsmul_cohomology_gsDiv_QZ (ιs : LocalEmbeddings K) {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology (gsDiv K S ιs QZ) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 :=
  eq_zero_of_pow_nsmul_cohomology_divFunRep (gsDecomp K S ιs) (continuous_gsDecomp K S ιs) hℓ (by omega)
    (fun v y hy => hy.elim fun j hj => eq_zero_of_pow_nsmul_cohomology_range_gsDecomp K S ιs v hℓ hS hp y j hj)
    x k hx


include hℓ hS in
theorem isIsoModCoprime_sUnitsToUnits_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    IsIsoModCoprime ℓ (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom :=
  isIsoModCoprime_sUnitsToUnits K S (nonempty_localEmbeddings K).some hℓ hS
    (fun _ hp x k hx => eq_zero_of_pow_nsmul_cohomology_gsDiv_QZ K S hℓ hS _ hp x k hx) hr


include hℓ hS in
theorem isIsoModCoprime_sUnitsInfl {r : ℕ} (hr : 4 ≤ r) : IsIsoModCoprime ℓ (sUnitsInfl K S r) :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS (by omega)).comp (isIsoModCoprime_sUnitsToUnits_of_four_le K S hℓ hS hr)

noncomputable def sUnitsToUnitsPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) ℓ :=
  AddEquiv.ofBijective _
    ((isIsoModCoprime_sUnitsToUnits_of_four_le K S hℓ hS hr).bijective_primaryComponentMap hℓ
      (isTorsion_cohomology _ (by omega)))

noncomputable def sUnitsInflPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) ℓ :=
  AddEquiv.ofBijective _
    ((isIsoModCoprime_sUnitsInfl K S hℓ hS hr).bijective_primaryComponentMap hℓ (isTorsion_cohomology _ (by omega)))

section Odd



end Odd

section Real

variable (ι : LocalEmbeddings K)

theorem mem_primaryComponent_two_unitsLimitRep {r : ℕ} (hr : 4 ≤ r) (y : cohomology (unitsLimitRep K) r) :
    y ∈ AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) 2 :=
  ⟨1, by rw [pow_one]; exact two_nsmul_cohomology_unitsLimitRep hr y⟩

theorem bijective_realLocalization_comp_primaryComponent {X : Type*} [AddCommGroup X] {r : ℕ} (hr : 4 ≤ r)
    (f : X →+ cohomology (unitsLimitRep K) r) (hf : IsIsoModCoprime 2 f) (hX : IsAddTorsion X) :
    Function.Bijective ((realLocalization ι (r := r) (by omega)).comp
      (f.comp (AddCommGroup.primaryComponent X 2).subtype)) := by
  have hb := hf.bijective_primaryComponentMap Nat.prime_two hX
  have hR := bijective_realLocalization ι hr
  refine ⟨fun a b hab => hb.1 (Subtype.ext (hR.1 hab)), fun t => ?_⟩
  obtain ⟨y, rfl⟩ := hR.2 t
  obtain ⟨a, ha⟩ := hb.2 ⟨y, mem_primaryComponent_two_unitsLimitRep (K := K) hr y⟩
  exact ⟨a, congrArg (realLocalization ι (r := r) (by omega)) (congrArg Subtype.val ha)⟩

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

noncomputable def gsUnitsRealPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) 2 ≃+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) :=
  AddEquiv.ofBijective _ (bijective_realLocalization_comp_primaryComponent K ι hr (gsUnitsInfl K S r)
    (isIsoModCoprime_gsUnitsInfl K S Nat.prime_two h2S (by omega)) (isTorsion_cohomology _ (by omega)))

noncomputable def sUnitsRealPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2 ≃+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) :=
  AddEquiv.ofBijective _ (bijective_realLocalization_comp_primaryComponent K ι hr (sUnitsInfl K S r)
    (isIsoModCoprime_sUnitsInfl K S Nat.prime_two h2S hr) (isTorsion_cohomology _ (by omega)))

theorem sUnitsRealPrimaryEquiv_apply {r : ℕ} (hr : 4 ≤ r)
    (x : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2) :
    sUnitsRealPrimaryEquiv K S ι h2S hr x = realLocalization ι (r := r) (by omega) (sUnitsInfl K S r x) :=
  rfl

end Real

end

end GroundTheory.ProfCoh
