module

public import Mathlib.RingTheory.Derivation.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem dvd_derivation_of_mem_span_prod_params :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (m : ℕ)
      (r : Fin m → R), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m r → ∀ (J : Finset (Fin m))
      (D : Derivation ℤ R R), D (∏ j ∈ J, r j) ∈ Ideal.span {∏ j ∈ J, r j} →
      ∀ j ∈ J, r j ∣ D (r j) := by
  intro R _ _ _ _ m r hrsp J D hD j hj
  have hprime : ∀ i, Prime (r i) :=
    ReciprocityTheory.AnForm.R.prime_of_regular_params r hrsp.1 hrsp.2
  have hnass : ∀ i k, i ≠ k → ¬ Associated (r i) (r k) :=
    (ReciprocityTheory.AnForm.R.regular_params_spec r hrsp.1 hrsp.2).2
  have hsplit : ∏ i ∈ J, r i = r j * ∏ i ∈ J.erase j, r i :=
    (Finset.mul_prod_erase J r hj).symm
  have hdvdD : r j ∣ D (∏ i ∈ J, r i) := by
    have h1 : (∏ i ∈ J, r i) ∣ D (∏ i ∈ J, r i) := Ideal.mem_span_singleton.mp hD
    exact (hsplit ▸ dvd_mul_right (r j) _ : r j ∣ ∏ i ∈ J, r i).trans h1
  rw [hsplit, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hdvdD
  have h2 : r j ∣ (∏ i ∈ J.erase j, r i) * D (r j) :=
    (dvd_add_right (dvd_mul_right (r j) _)).mp hdvdD
  rcases (hprime j).dvd_or_dvd h2 with h3 | h3
  · exfalso
    obtain ⟨k, hk, hdk⟩ := (hprime j).exists_mem_finset_dvd h3
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    exact hnass j k (Ne.symm hkj) ((hprime j).associated_of_dvd (hprime k) hdk)
  · exact h3

end GlobalTheory
