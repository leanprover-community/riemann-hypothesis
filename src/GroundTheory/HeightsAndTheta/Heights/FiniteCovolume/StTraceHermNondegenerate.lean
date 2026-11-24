module

public import GroundTheory.AutomorphicForms.HermitianSpaces
public import Mathlib.NumberTheory.NumberField.Basic
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

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

def traceHerm (h : HermitianForm F E W) (v : Basis ι E W) : LinearMap.BilinForm ℚ (ι → E) :=
  LinearMap.mk₂ ℚ
    (fun y z => Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)))
    (fun y₁ y₂ z => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • y) = (algebraMap ℚ E c) • v.equivFun.symm y := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      have e2 : conjHom F E (algebraMap ℚ E c) = algebraMap ℚ E c :=
        RingHom.map_rat_algebraMap _ _
      rw [e1, LinearMap.map_smulₛₗ₂, e2, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul,
        smul_eq_mul])
    (fun y z₁ z₂ => by simp only [map_add (f := _)])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • z) = (algebraMap ℚ E c) • v.equivFun.symm z := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      rw [e1, LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])

theorem traceHerm_apply (h : HermitianForm F E W) (v : Basis ι E W) (y z : ι → E) :
    traceHerm h v y z = Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)) := rfl

def TraceHermNondegenerate.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  (traceHerm h v).Nondegenerate

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
