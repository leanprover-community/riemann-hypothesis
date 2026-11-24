module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CoeffSpace

theorem nontrivial_VV : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), Nontrivial (Formalism.L2.DIV.VV K lam) := by
  intro K _ ι _ n lam
  have hanti : ∀ τ, Antitone (lam τ).natW := fun τ i j hij =>
    Int.toNat_le_toNat (by have := (lam τ).anti hij; omega)
  have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) ∈ Formalism.L2.DIV.VV K lam :=
    Submodule.subset_span ⟨fun τ => Formalism.BasicNotions.extremal K n (lam τ),
      fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (hanti τ), rfl⟩
  refine ⟨⟨⟨_, hmem⟩, 0, fun h => ?_⟩⟩
  have h0 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) = 0 := congrArg Subtype.val h
  rw [Finset.prod_eq_zero_iff] at h0
  obtain ⟨τ, _, h⟩ := h0
  have hinj : Function.Injective (fun v : Fin n × Fin n => (τ, v)) := fun a b hab => (Prod.mk.inj hab).2
  exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl _ (MvPolynomial.rename_injective _ hinj (h.trans (map_zero _).symm))

end GlobalTheory.CoeffSpace
