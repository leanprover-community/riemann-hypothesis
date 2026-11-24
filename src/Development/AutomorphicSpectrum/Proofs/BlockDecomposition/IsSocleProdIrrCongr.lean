module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLSegSingle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSingleRev
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isSocle_prodIrr_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {y z : Fin h → IrrGL (k := k)} (e : y = z)
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) (H : IsSocle π (prodIrr y hy)) :
    IsSocle π (prodIrr z hz) := by
  subst e
  exact H

theorem socleOne : PositivityTheory.SphericalProduct.SocleOne := by
  intro k _ _ _ _ _ n ξ hξ hanti hd
  let x : Fin n → IrrGL (k := k) := fun i =>
    IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))
  have hLF : LFactors (PositivityTheory.SphericalProduct.msOne ξ hξ) x :=
    ⟨_, GlobalTheory.CompanionTheory.OneTermOrder.isOrderedForm_single_rev k n ξ hξ hanti, fun i => isLSeg_single k _ _⟩
  have hd1 : ∑ a, (x a).1 = n := by simp [x, IrrGL.ofChar]
  have hd2 : ∑ a, (x (Fin.rev a)).1 = n := by simp [x, IrrGL.ofChar]
  refine ⟨?_, ?_⟩
  · obtain ⟨π, hπ⟩ := PositivityTheory.Exh.standardCosocleGL_holds k _ n n x hd1 hLF
    have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π.ρ := ⟨n, x, hd1, hLF, hπ⟩
    exact ⟨IrrGL.of π.ρ π.smooth π.irr, rfl, hL.of_equiv (IrrGL.equivOf _ _ _)⟩
  · intro V _ _ π hL
    have hS := PositivityTheory.Exh.lSocleGL_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ n n x hd2 hLF π hL
    refine isSocle_prodIrr_congr ?_ _ hd hS
    funext a
    simp only [x, Function.comp, Fin.rev_rev]

end GlobalTheory.CompanionTheory.LocGL
