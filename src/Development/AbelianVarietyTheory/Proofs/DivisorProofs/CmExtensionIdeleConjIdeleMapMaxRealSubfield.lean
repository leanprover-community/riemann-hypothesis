module

public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ConjIdeleReal

theorem adeleMap_eq_baseChange (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L = GroundTheory.Global.AdeleBaseChange.adeleMap K L := by
  ext a : 1
  apply Prod.ext
  · funext w
    open scoped NumberField.LiesOver in
    change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
    rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
  · apply FiniteAdeleRing.ext
    intro w
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w _ =
      GroundTheory.Global.SemiLocal.completionMap _ w _
    rfl

theorem ideleConj_ideleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b := by
  intro E _ _ _ b
  let alg : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have tw : @IsScalarTower (maximalRealSubfield E) E E _ (@Algebra.toSMul _ _ _ _ alg) _ :=
    @IsScalarTower.of_algebraMap_eq (maximalRealSubfield E) E E _ _ _ _ alg _ fun x =>
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x).symm
  have h := @GroundTheory.Global.AdeleBaseChange.adeleMap_adeleMap (maximalRealSubfield E) E E _ _ _ _ _ _ _ alg _ tw
    (b : AdeleRing _ _)
  rw [← adeleMap_eq_baseChange, ← adeleMap_eq_baseChange] at h
  apply Units.ext
  exact h

end GlobalTheory.ConjIdeleReal
