module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialCycleEval
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealSurj
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem VNumCut.proof (h : CutByForm.Statement.{u}) : VNumCut.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ G n hGp hGh hϖG hdim s c hs hsG bs
  set π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hπ
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => rfl
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := ker_map_residue_eq_span hϖ

  have hGbp : (specialIdeal G).IsPrime :=
    (SpecialIdealCorresp.proof O ϖ hϖ K ι G G hGp hϖG).1
  have hGbh : IsMultiHomogIdeal (specialIdeal G) := SpecialIdealMultiHomog.proof O K ι G hGh
  have hdimb : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal G) <
      ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.proof O ϖ hϖ K ι G hϖG]; exact hdim
  have hsb : IsMultiHomog (π s) c := isWeightedHomogeneous_map_of _ _ hs
  have hsbG : π s ∉ specialIdeal G := by
    intro hm
    apply hsG
    have hcm : (G.map π).comap π = G := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker, sup_eq_left, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hϖG
    rw [← hcm]
    exact hm

  have hcut := h (IsLocalRing.ResidueField O) K ι n (specialIdeal G) hGbp hGbh hdimb (π s) c hsb
    hsbG bs

  have hJ : G ⊔ Ideal.span {s} ⊔ Ideal.span {C ϖ} = G ⊔ Ideal.span {s} := by
    rw [sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left hϖG
  have hdiv : divCycle G s = divCycle (G ⊔ Ideal.span {s}) (C ϖ) := by
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hJ]
  have hmapJ : specialIdeal (G ⊔ Ideal.span {s}) = specialIdeal G ⊔ Ideal.span {π s} := by
    rw [hsp, hsp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have htr := SpecialCycleEval.proof SpecialIdealCorresp.proof SpecialIdealSurj.proof
    SpecialMultAt.proof O ϖ hϖ K ι (G ⊔ Ideal.span {s})
    (fun V => intNum (IsLocalRing.ResidueField O) V bs)
  rw [hmapJ, ← divCycle_eq_idealCycle] at htr
  show intNum (IsLocalRing.ResidueField O) (specialIdeal G) _ =
    cycEval (fun U => intNum (IsLocalRing.ResidueField O) (specialIdeal U) bs) (divCycle G s)
  rw [hcut, hdiv, htr]

end GroundTheory.Heights₂.Heights.NumbersDVR
