module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffOfNotXPowDvdLine
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.exists_unit_coeff_of_not_X_pow_dvd_line : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [Algebra (X.O0 i) K], IsRes i K → ∀ (b : ι → K) (n : ℕ), n ≤ X.l i ^ M → ∀ F G : MvPolynomial ι (X.O0 i), toLam X i M ι F = toLam X i M ι G → ¬ (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) G → ∃ m : ι →₀ ℕ, m.degree < n ∧ IsUnit (F.coeff m) := by
  first | exact @GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | exact GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | (intros; apply GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line <;> assumption)
