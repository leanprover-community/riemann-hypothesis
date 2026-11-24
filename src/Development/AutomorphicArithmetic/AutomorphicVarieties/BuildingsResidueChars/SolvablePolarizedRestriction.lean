module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_polarized_restriction :
    UpperTheory.V.Af.Sol.PolRes := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r h
  obtain ⟨F₀, i1, i2, i3, i4, i5, i6, hF, μ, c, P, hμ, hs, hc, hp⟩ := h
  letI : Algebra F₀ M := ((algebraMap K M).comp (algebraMap F₀ K)).toAlgebra
  haveI : IsScalarTower F₀ K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower F₀ M Ω := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply F₀ K Ω,
      IsScalarTower.algebraMap_apply K M Ω]
  refine ⟨F₀, i1, i2, inferInstance, inferInstance, this, i6, hF, μ, c, P, hμ, hs, hc, ?_⟩
  unfold IsPairing at hp ⊢
  intro t t' ht
  have e1 : ∀ u : G M Ω,
      AlgEquiv.restrictScalars F₀ (resG K M Ω u) = AlgEquiv.restrictScalars F₀ u := by
    intro u; ext x; rfl
  have e2 : ∀ u : G M Ω, resG F₀ M Ω u = resG F₀ K Ω (resG K M Ω u) := by
    intro u; ext x; rfl
  have key := hp (resG K M Ω t) (resG K M Ω t') (by rw [e1, e1]; exact ht)
  simpa [e2] using key
