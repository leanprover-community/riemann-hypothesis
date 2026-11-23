module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsCuspidalSatakeAtPrimeToLevelOfNewform
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

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem frobRoot_alt : _root_.UpperTheory.V.Af.Hypotheses' → LocQ → FrobRoot := by
  intro P hQ l _ Ω _ _ _ ι e V A κ g hl he hc hirr hdet hA hex hatt hgM σ hσ
  obtain ⟨π, hreg, hπ, hsat⟩ := _root_.GlobalTheory.T.exists_cuspidal_attached_satake_eq_hecke_poly_of_not_dvd P e g l Ω ι V he hatt hgM
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨B, hB, hpoly⟩ := hsat v hlv
  obtain ⟨b, hb, hrel⟩ :=
    (hQ l hl Ω ι e he V π hc hirr hdet hreg hπ v A κ hlv hv hex (Or.inr ⟨B, hB⟩)).2 B hB σ hσ
  refine ⟨(l : ℂ) ^ e * b, ?_, Or.inr ?_⟩
  · rw [← hpoly, Polynomial.IsRoot, Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map_of_mem _ hb, ?_⟩)
    simp
  · refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [zpow_natCast] at hrel
    linear_combination hrel
end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end
