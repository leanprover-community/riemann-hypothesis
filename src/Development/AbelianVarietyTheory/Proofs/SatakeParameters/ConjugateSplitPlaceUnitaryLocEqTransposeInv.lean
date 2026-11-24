module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open TensorProduct

namespace GlobalTheory.ConjLoc

theorem proj_conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (a : AL L) :
    (GlobalTheory.TypeTame.conjSP s).proj a = s.proj (conjAL L a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x b =>
    simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_conjSP : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (x : GAf L n), ((GlobalTheory.TypeTame.conjSP s).loc n x).val = ((s.loc n x)⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose := by
  intro L _ _ _ n s x
  have hx : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h1 : (s.loc n x).val * ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose = 1 := by
    have e : ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose
        = (conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L))).map s.proj := by
      refine Matrix.ext fun i j => ?_
      exact proj_conjSP s _
    have e' : (s.loc n x).val = (x.1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj := rfl
    rw [e, e', ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 := Units.inv_eq_of_mul_eq_one_right h1
  rw [h2, Matrix.transpose_transpose]

end GlobalTheory.ConjLoc
