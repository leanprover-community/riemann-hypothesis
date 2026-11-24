module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLevelOfFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClassesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductEqFinprodStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryGeometricSideSeparableTest
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

@[expose] public section

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

theorem UpperTheory.V.Z.Mult.geomTr :
    UpperTheory.V.Z.Mult.GeomTr := by
  intro E _ _ _ hU n hn S hS lam K' hK'
  refine ⟨dimW_ne_zero lam, fun f hf hsep => ?_⟩
  have hOrb : geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) =
      geomURat lam (fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) := by
    unfold geomURat
    refine finsum_congr fun c => ?_
    split_ifs with hc
    · exact congrArg (_ * ·) (GlobalTheory.T.twistedOrbitalIntegral_product_eq_finprod E hU n hn S hS K' hK' f hf c.rep hc)
    · rfl
  rw [GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses E hU n hn S hS lam K' hK' f hf hsep, hOrb,
    GlobalTheory.PreStabU.geomURat_eq_geomU E hU n hn S hS lam K' hK' f hf hsep]
