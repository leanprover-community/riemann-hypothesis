module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SxExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Stabfin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField UpperTheory.V UpperTheory.V.Af.BA

private noncomputable def cxK (L : Type) [Field L] [NumberField L] (N : ℕ) : Cx (KT.Gm L N) (KT.Vx L N) where
  S := ConeExtensionAcyclic.simp (KT.qc L N) (KT.Psd L N)
  comp := fun f t ht => by
    obtain ⟨y, hy, h⟩ := ht
    exact ⟨y, hy, fun j => h (f j)⟩
  smul := fun g t ht => KT.smul_mem_simp g ht

theorem UpperTheory.bounded_complex_of_bounded_simplicial_complex :
    UpperTheory.V.Af.BA.BddCx → UpperTheory.V.Af.BA.BddComplex := by
  intro H L _ _ _ N
  refine H (KT.Gm L N) (KT.Vx L N) (cxK L N) (fun m => ConeExtensionAcyclic.sx_exact L N m) (fun p => ?_) (fun t => ?_)
  · haveI : Finite (MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p)) := (KT.orb L N p).1
    refine ⟨Set.range (fun c : MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p) => Quotient.out c),
      Set.finite_range _, fun x => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (KT.Gm L N) ((cxK L N).Tup p)) x)))
    exact ⟨g, _, hg.symm⟩
  · haveI := KT.stabfin L N (t.1 0)
    refine Finite.of_injective (fun g : MulAction.stabilizer (KT.Gm L N) t =>
      (⟨g.1, congrFun (congrArg Subtype.val g.2) 0⟩ : MulAction.stabilizer (KT.Gm L N) (t.1 0))) fun g k e => ?_
    exact Subtype.ext (Subtype.mk.inj e)
