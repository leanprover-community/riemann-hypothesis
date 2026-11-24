module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceSingleEndomorphism
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.Pass.CutEq

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem main : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i),
    PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  intro D i Xs π
  have h : ccAt (D.nd.T i) (cutLocus i Xs) π = GlobalTheory.Cut.ccOff i Xs π := by
    unfold ccAt GlobalTheory.Cut.ccOff Ideal.map
    congr 1
    ext a
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f.1, f.2, fun x hx hZ => ?_, rfl⟩
      have := congrFun (RingHom.mem_ker.1 hf) ⟨x, by simp [cutLocus, hx, hZ]⟩
      exact this
    · rintro ⟨f, hf, h0, rfl⟩
      refine ⟨⟨f, hf⟩, RingHom.mem_ker.2 (funext fun y => ?_), rfl⟩
      have hy := y.2
      simp only [cutLocus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hy
      exact h0 y.1 hy.2 hy.1
  unfold vccCut GlobalTheory.Cut.vccOff
  rw [h]

end GlobalTheory.Pass.CutEq
