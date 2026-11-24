module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.finiteCharacter_of_algebraic_cyclotomic :
    UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Af.Sol.FinChar := by
  intro hA
  refine ⟨?_, ?_⟩
  · intro F Ω _ _ _ _ _ l _ ι δ hopen
    obtain ⟨h1, -, -⟩ := hA F Ω l ι
    have hcont : Continuous δ := by
      refine continuous_of_continuousAt_one δ ?_
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hopen.mem_nhds (Subgroup.one_mem _)] with x hx
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      rw [hx, map_one]
    haveI : Finite (Formalism.ConjugateSelfDual.G F Ω ⧸ δ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
    haveI : δ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    refine h1 δ hcont fun w _ => ?_
    obtain ⟨A, hAw⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hAw, 0, δ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun s _ => ?_⟩
    rw [neg_zero, zpow_zero, mul_one, ← map_pow]
    exact Subgroup.pow_index_mem δ.ker s
  · intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ
    let E : IntermediateField K Ω := (IsScalarTower.toAlgHom K M Ω).fieldRange
    haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
    haveI : FiniteDimensional K E :=
      LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M Ω)).toLinearEquiv
    refine Subgroup.isOpen_mono ?_ E.fixingSubgroup_isOpen
    intro g hg
    have hfix : ∀ m : M, g (algebraMap M Ω m) = algebraMap M Ω m := by
      intro m
      exact (IntermediateField.mem_fixingSubgroup_iff E g).mp hg _ ⟨m, rfl⟩
    let g' : Formalism.ConjugateSelfDual.G M Ω := { g.toRingEquiv with commutes' := hfix }
    have hres : UpperTheory.V.Af.resG K M Ω g' = g := by
      ext x; rfl
    rw [MonoidHom.mem_ker, ← hres, ← MonoidHom.comp_apply, hδ, MonoidHom.one_apply]
