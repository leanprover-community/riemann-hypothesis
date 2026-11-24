module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Int.Core

theorem ramUnr_holds : RamUnr := by
  intro F Ω _ _ _ _ _ T Q hQ
  obtain ⟨u, huT, A, hA, τ, hτ, hfix⟩ := hQ
  haveI : Algebra.IsQuadraticExtension F ↥Q.K := ⟨Q.two⟩
  haveI : IsGalois F ↥Q.K := inferInstance
  obtain ⟨w, hw, hwu⟩ := CompanionTheory.FamInh.exists_place_between (K := F) (L := ↥Q.K) hA
  have hunder : w.under (𝓞 F) = u :=
    ReciprocityTheory.Gal.eq_of_isPlaceOver (fun x => by
      rw [IsScalarTower.algebraMap_apply F ↥Q.K Ω]
      exact hw (algebraMap (𝓞 F) (𝓞 ↥Q.K) x)) hA
  refine ⟨w, fun hun => hfix fun x => ?_, hunder ▸ huT⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hs := CompanionTheory.FamInh.res_mem_inertia (L := ↥Q.K) hw hτ
  rw [(CompanionTheory.FamInh.inertia_eq_bot_iff u w).2 he, Subgroup.mem_bot] at hs
  have hc := AlgEquiv.restrictNormal_commutes τ ↥Q.K x
  have h1 : AlgEquiv.restrictNormal τ ↥Q.K x = x := DFunLike.congr_fun hs x
  rw [h1] at hc
  exact hc.symm

end UpperTheory.Gal.Int.Core
