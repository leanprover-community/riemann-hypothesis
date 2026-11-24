module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

theorem _root_.GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  first | (exact @GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (exact GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (intros; apply GlobalTheory.RSNonvan.norm_prod_sat_eq_one  <;> assumption)
