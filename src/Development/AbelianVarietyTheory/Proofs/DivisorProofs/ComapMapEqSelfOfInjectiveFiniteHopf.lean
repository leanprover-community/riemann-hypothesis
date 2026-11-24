module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanEqTopOfFinrankFibreEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsGroup
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

@[expose] public section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDiv

theorem faithfullyFlat_range_of_hopf_finite (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    Module.FaithfullyFlat (AlgHom.range (f : B →ₐ[k] A)) A := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  haveI : Module.Finite k (AlgHom.range (f : B →ₐ[k] A)) :=
    Module.Finite.of_injective (AlgHom.range (f : B →ₐ[k] A)).val.toLinearMap
      Subtype.val_injective
  haveI : Module.Finite (AlgHom.range (f : B →ₐ[k] A)) A :=
    Module.Finite.of_restrictScalars_finite k _ A
  haveI : IsArtinianRing (AlgHom.range (f : B →ₐ[k] A)) := IsArtinianRing.of_finite k _
  obtain ⟨b⟩ := GlobalTheory.nonempty_basis_of_basis_baseChange (B := AlgHom.range (f : B →ₐ[k] A))
    (A := A) (M := A) Subtype.val_injective (((Module.finBasis k _).baseChange A).map e.symm)
  haveI := Module.Free.of_basis b
  haveI : Nontrivial A := (counitAlgHom k A).domain_nontrivial
  infer_instance

theorem comap_map_eq_self_of_hopf_injective : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  intro k A B _ _ _ _ _ _ f hf J
  haveI := faithfullyFlat_range_of_hopf_finite k A B f
  let g : B →+* AlgHom.range (f : B →ₐ[k] A) := (f : B →ₐ[k] A).rangeRestrict.toRingHom
  have hg : Function.Bijective g :=
    ⟨fun x y h => hf (congrArg Subtype.val h), (f : B →ₐ[k] A).rangeRestrict_surjective⟩
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) (Ideal.map g J)
  rw [Ideal.map_map] at h
  have h2 := congrArg (Ideal.comap g) h
  rw [Ideal.comap_comap, Ideal.comap_map_of_bijective g hg] at h2
  exact h2

end GlobalTheory.PDiv
