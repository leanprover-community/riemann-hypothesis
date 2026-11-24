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

theorem UpperTheory.galois_representation_image_spec :
    UpperTheory.V.Af.Sol.GalRange := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  let ρ : Gal(Ω/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hker : (resG K M Ω).range = ρ.ker := by
    ext σ
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨τ, rfl⟩
      ext x
      apply (algebraMap M Ω).injective
      rw [show (ρ (resG K M Ω τ)) = (resG K M Ω τ).restrictNormal M from rfl,
        AlgEquiv.restrictNormal_commutes]
      simp [resG]
    · intro h
      have hfix : ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω x := by
        intro x
        have := AlgEquiv.restrictNormal_commutes σ M x
        rw [show σ.restrictNormal M = ρ σ from rfl, h] at this
        simpa using this.symm
      refine ⟨{ σ.toRingEquiv with commutes' := hfix }, ?_⟩
      ext x
      rfl
  refine ⟨hker ▸ ρ.normal_ker, ?_⟩
  rw [hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) Ω),
    Subgroup.card_top, IsGalois.card_aut_eq_finrank]
