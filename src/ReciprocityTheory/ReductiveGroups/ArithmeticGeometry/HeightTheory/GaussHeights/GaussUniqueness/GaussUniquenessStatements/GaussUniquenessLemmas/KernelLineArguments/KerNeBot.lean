module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.NotInjOfTrdeg
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem ker_ne_bot (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (ha : ∀ j, a j ∈ vRing v) (hD : 1 ≤ D)
    (htr : letI := resAlg (F := K) v
      let L := IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
        {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}
      letI := L.toSubalgebra.algebra
      Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) L =
        ((D - 1 : ℕ) : Cardinal)) :
    RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) ≠ ⊥ := by
  let := resAlg (F := K) v
  intro hbot
  let S : Set (IsLocalRing.ResidueField (vRing v)) :=
    {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}
  let ρL : Fin N → IntermediateField.adjoin
      (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S :=
    fun k => ⟨IsLocalRing.residue (vRing v) ⟨a (j0.succAbove k), ha _⟩,
      IntermediateField.subset_adjoin _ _ ⟨j0.succAbove k, ha _, rfl⟩⟩
  have hni := not_inj_of_trdeg (D := D) S j0 ρL hD htr
  rw [injective_iff_map_eq_zero] at hni
  push Not at hni
  obtain ⟨G, hG0, hG⟩ := hni
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective (gK v hv) (gK_surj v hv) G
  have hf : f ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  have H : psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) =
      (MvPolynomial.map (algebraMap (IntermediateField.adjoin
        (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S)
        (IsLocalRing.ResidueField (vRing v)))).comp
        (((MvPolynomial.aeval (imgR (D := D) j0 ρL)).toRingHom).comp
          (MvPolynomial.map (gK v hv))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply]
      congr 1
    · intro t
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      rw [imgR_map, imgR_map]
      rfl
  have hmem : f ∈ RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    rw [RingHom.mem_ker, H]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hG0, map_zero]
  rw [hbot] at hmem
  exact hf (Ideal.mem_bot.mp hmem)

end GaussValuationUniqueness
