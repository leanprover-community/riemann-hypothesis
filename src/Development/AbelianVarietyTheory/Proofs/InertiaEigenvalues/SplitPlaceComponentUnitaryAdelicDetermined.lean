module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfSupportedAtSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
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

namespace GlobalTheory.SplitCompat

theorem compAt_eq_zero_of_proj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : AL L) (hp : s.proj z = 0) (hq : s.proj (conjAL L z) = 0) : compAt L s.v z = 0 := by
  obtain ⟨e, hne⟩ : ∃ e : L, e ≠ IsCMField.complexConj L e := by
    by_contra hcon
    push Not at hcon
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => (hcon x).symm)
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), e] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * (e - IsCMField.complexConj L e) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = e := by simp [b]
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have h1 : s.proj z = A s.v + s.i e * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L e) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : s.i e - s.i (IsCMField.complexConj L e) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hne (s.i.toRingHom.injective h)
  have hBv : B s.v = 0 := by
    have hm : (s.i e - s.i (IsCMField.complexConj L e)) * B s.v =
        s.proj z - s.proj (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    rw [hp, hq, sub_zero] at hm
    exact (mul_eq_zero.1 hm).resolve_left hu
  have hAv : A s.v = 0 := by
    rw [hp, hBv, mul_zero, add_zero] at h1
    exact h1.symm
  rw [hAB]
  have hA' : evalAt L s.v A = 0 := by rw [← hAv]; rfl
  have hB' : evalAt L s.v B = 0 := by rw [← hBv]; rfl
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul, hA', hB']

theorem compAt_map_eq_of_loc_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (x y : GAf L n), s.loc n x = s.loc n y →
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) =
        (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) := by
  intro L _ _ _ n s x y h
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  rw [← sub_eq_zero, ← map_sub]
  apply compAt_eq_zero_of_proj_eq_zero s
  · rw [map_sub, GlobalTheory.SplitLocEq.proj_entry, GlobalTheory.SplitLocEq.proj_entry, h, sub_self]
  · rw [map_sub, map_sub, GlobalTheory.SplitLocEq.conj_entry, GlobalTheory.SplitLocEq.conj_entry, GlobalTheory.SplitLocEq.proj_entry,
      GlobalTheory.SplitLocEq.proj_entry, map_inv, map_inv, h, sub_self]

end GlobalTheory.SplitCompat
