module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace UnramifiedTwist

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have h1 := LinearMap.charpoly_sub_smul (c • (1 : Module.End ℂ V)) c
  rw [sub_self, LinearMap.charpoly_zero] at h1
  calc (c • (1 : Module.End ℂ V)).charpoly
      = ((c • (1 : Module.End ℂ V)).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [Polynomial.comp_assoc]; simp
    _ = (X - C c) ^ Module.finrank ℂ V := by rw [← h1, Polynomial.X_pow_comp]

theorem diagEnd_const (c : ℂ) :
    diagEnd (fun _ : Fin 1 => c) = c • (1 : Module.End ℂ (Fin 1 → ℂ)) :=
  LinearMap.ext fun v => funext fun i => by simp

end UnramifiedTwist

open UnramifiedTwist in
theorem step_unrTwist : UnramifiedTwistProp := by
  intro E Ω _ _ _ _ _ A w h u ψ hψ hu
  obtain ⟨n, a, rfl⟩ := WD.exists_rep u
  rw [WD.unr_mk] at hu
  obtain ⟨hN, hI⟩ := hu
  simp only [WD.lpOfChar, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.charPol_mk, WD.lpDim_mk]
  refine ⟨?_, fun t => ?_⟩
  · rw [WDRep.tensor_N, hN, WDRep.ofChars_N]
    simp
  · rw [WDRep.tensor_ρ, hI t, WDRep.ofChars_ρ, diagEnd_const, TensorProduct.map_smul_right,
      TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct]
    simp

end UpperTheory.TNZ
