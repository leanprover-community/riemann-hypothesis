module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TrivOutsideGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem coe_mul_mat (x y : GAf L n) :
    ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl

theorem map_inv_mul_map (x : GAf L n) (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 := by
  rw [← Matrix.map_mul, ← coe_mul_mat, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem map_inv_eq_one (x : GAf L n) (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1) :
    ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 := by
  have := map_inv_mul_map x w
  rwa [h, mul_one] at this

theorem adele_eq_zero (z : AL L) (hz : ∀ w, compAt L w z = 0) : z = 0 := by
  have hcard : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _ hcard
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  have hw : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB] at h
    apply GlobalTheory.tensor_decomp_eq_zero b
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have hA : A = 0 := DFunLike.ext _ _ fun w => (hw w).1
  have hB : B = 0 := DFunLike.ext _ _ fun w => (hw w).2
  rw [hAB, hA, hB]
  simp

theorem eq_one_of_trivOutside_empty (y : GAf L n) (hy : TrivOutside (∅ : Set _) y) : y = 1 := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [← sub_eq_zero]
  apply adele_eq_zero
  intro w
  have h1 := congrFun (congrFun (hy w (Set.notMem_empty w)) i) j
  simp only [Matrix.map_apply] at h1
  rw [map_sub, h1]
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_of_trivOutside_of_local : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (K : Subgroup (GAf L n)) (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) (y : GAf L n), TrivOutside (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) y → (∀ v ∈ T, ∃ p ∈ K, TrivOutside {v} p ∧ (p.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v)) → y ∈ K := by
  intro L _ _ _ n K T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro y hy _
    rw [eq_one_of_trivOutside_empty y (by simpa using hy)]
    exact K.one_mem
  | insert v T hv ih =>
    intro y hy hloc
    obtain ⟨p, hpK, hpT, hpv⟩ := hloc v (Finset.mem_insert_self v T)
    have hpinv : ∀ w, w ≠ v → ((p⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 :=
      fun w hw => map_inv_eq_one p w (hpT w (by simpa using hw))
    have key : y = p * (p⁻¹ * y) := by group
    rw [key]
    refine K.mul_mem hpK (ih _ ?_ ?_)
    · intro w hw
      rw [coe_mul_mat, Matrix.map_mul]
      by_cases hwv : w = v
      · subst hwv
        rw [← hpv, map_inv_mul_map]
      · have hwT : w ∉ ((insert v T : Finset _) : Set _) := by
          simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
          exact ⟨hwv, hw⟩
        rw [hpinv w hwv, hy w hwT, mul_one]
    · intro w hw
      obtain ⟨q, hqK, hqT, hqw⟩ := hloc w (Finset.mem_insert_of_mem hw)
      refine ⟨q, hqK, hqT, ?_⟩
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [hqw, coe_mul_mat, Matrix.map_mul, hpinv w hwv, one_mul]

end GlobalTheory.TrivOutsideGen
