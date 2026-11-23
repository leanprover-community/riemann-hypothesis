module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.ConeFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.DualConvex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.ExistsVert
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveConvex
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_simp : ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → FaceClosed (simp q T) ∧ simp q T 0 = univ ∧ Acyc (simp q T) := by
  intro E Y _ _ _ q T hG
  refine ⟨UpperTheory.V.ConeExtensionAcyclic.nerve_faceClosed _ _, ?_, ?_⟩
  · ext t
    simp only [UpperTheory.V.ConeExtensionAcyclic.simp, UpperTheory.V.ConeExtensionAcyclic.nerve, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := hG.pos
    exact ⟨x, hx, fun j => j.elim0⟩
  · exact UpperTheory.V.ConeExtensionAcyclic.nerve_convex _ _ (UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).1 hG.pos
      (fun v => ((UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).2 _).1)
      (fun v => ((UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).2 _).2)
      (UpperTheory.V.ConeExtensionAcyclic.cone_finite hG) (UpperTheory.V.ConeExtensionAcyclic.exists_vert hG)
