module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
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
import Mathlib.Tactic.NormNum.Prime
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSGalAdEx
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.IsGalAd

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Places

private theorem infOf_ne {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) : infOf m ≠ infOf m' := by
  intro e
  have h1 : (((2 : ℕ) : ℂ) - 1) / 2 + (m 0 : ℂ) ∈ infOf m := Multiset.mem_map.2 ⟨0, Finset.mem_univ_val _, rfl⟩
  rw [e] at h1
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 h1
  have h2 : m' i = m 0 := Int.cast_injective (add_left_cancel hi)
  fin_cases i
  · exact absurd (@h 2 0 h2) (by decide)
  · exact absurd (@h 3 0 h2) (by decide)

open UpperTheory.CBC UpperTheory.CBC.SConjSpaceCAux in
private theorem not_conjIso {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    [IsGalois K M] (π : CuspSub M 2) (hm : MixWtC K π) : ¬ ∀ σ : M ≃ₐ[K] M, (Cusp.cx π).ConjIso σ.toRingEquiv := by
  intro h
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨m, m', τ, τ', -, h1, h2, k1, k2, hinj⟩ := hm φ
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) τ τ' (h1.trans h2.symm)
  obtain ⟨s, hs⟩ := SGalAdEx_holds M σ.toRingEquiv
  obtain ⟨P', hsp, hiso⟩ := h σ s hs
  obtain ⟨d, hd, hd'⟩ := exists_GD _ s hs
  cases P' with
  | re π' => exact hiso.elim
  | cx π' =>
    have e : τ.comp (d.σ.symm : M →+* M) = τ' := by
      rw [hd']
      exact hσ
    have k3 : π'.HasInfChar τ (infOf m') := by
      refine ⟨k2.1, fun u x hx => ?_⟩
      have hx' : x.1 ∈ (Cusp.cx π').space := ⟨x, hx, rfl⟩
      rw [hsp] at hx'
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx'
      obtain rfl : x = pull d 2 y := Subtype.ext (by rw [← hxy, ← hd]; rfl)
      rw [cap_pull, e, k2.2 u y hy, map_smul]
    exact infOf_ne hinj (k1.unique (CuspSub.Iso.hasInfChar hiso k3))
