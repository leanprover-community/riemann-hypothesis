module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section Loc

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    Subalgebra F (FractionRing (MRing ι F ⧸ P)) :=
  Algebra.adjoin F {x | ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
    g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}

theorem div_mem_degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F)))
    {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) (hgP : g ∉ P)
    (hg𝒲 : ∀ W ∈ 𝒲, g ∉ W) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ degZeroLoc P 𝒲 :=
  Algebra.subset_adjoin ⟨b, f, g, hf, hg, hgP, hg𝒲, rfl⟩

end Loc

section Fibre

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

def fibrePrimes (P' : Ideal (MRing ι' F)) (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Set (Ideal (MRing ι' F)) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ contractPrime j W' = W}

theorem map_degZeroLoc_le (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    (degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P') ≤
      degZeroLoc P' (fibrePrimes j P' W) := by
  unfold degZeroLoc
  rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_, ?_⟩
  · rintro W' ⟨-, -, hc⟩ hgW'
    apply hgW W (Set.mem_singleton W)
    rw [← hc]
    exact hgW'
  · rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]

def degZeroLocContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    degZeroLoc (contractPrime j P') {W} →ₐ[F] degZeroLoc P' (fibrePrimes j P' W) :=
  ((contractFracMap j P').comp (degZeroLoc (contractPrime j P') {W}).val).codRestrict _
    (fun x => map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩))

instance degZeroLoc.algebraContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Algebra (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) :=
  (degZeroLocContract j P' W).toRingHom.toAlgebra

theorem degZeroLoc.algebraMap_contract_coe (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (x : degZeroLoc (contractPrime j P') {W}) :
    ((algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) x :
      degZeroLoc P' (fibrePrimes j P' W)) : FractionRing (MRing ι' F ⧸ P')) =
      contractFracMap j P' x :=
  rfl

end Fibre

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
