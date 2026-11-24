module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.eigTransfer_holds :
    EigTransfer := by
  intro Γ k _ _ _ _ N N' ρ ρ' hρ hρ' hcp c ⟨v, hv0, hv⟩
  have hN : N = N' := by
    have h := congrArg Polynomial.natDegree (hcp 1)
    simpa [cp, Matrix.charpoly_natDegree_eq_dim] using h
  subst hN
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ ρ' hρ hρ' (fun g => hcp g)
  refine ⟨(P : Matrix (Fin N) (Fin N) k).mulVec v, ?_, ?_⟩
  · intro h
    apply hv0
    have := congrArg (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec) h
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · intro g
    have hg : ρ g * P = P * ρ' g := by
      rw [hP g]
      group
    have hm : (ρ g : Matrix (Fin N) (Fin N) k) * P = P * ρ' g := by
      rw [← Units.val_mul, hg, Units.val_mul]
    rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]
