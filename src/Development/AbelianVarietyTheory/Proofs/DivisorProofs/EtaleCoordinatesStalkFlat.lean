module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}}
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U →
    _root_.GlobalTheory.LogPair.IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U),
    ((Y.presheaf.germ U y hy).hom.comp (_root_.GlobalTheory.LogPair.cstOn g U)).Flat := by
  intro R _ Y g U n t hU ht y hy
  have hC : (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have hE : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Flat := by
    have h : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Etale := ht
    letI := (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(Y, U) := h
    show Module.Flat _ _
    infer_instance
  have hG : (Y.presheaf.germ U y hy).hom.Flat := by
    letI := (Y.presheaf.germ U y hy).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨y, hy⟩
    show Module.Flat _ _
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  rw [← MvPolynomial.eval₂Hom_comp_C (_root_.GlobalTheory.LogPair.cstOn g U) t, ← RingHom.comp_assoc]
  exact (hC.comp hE).comp hG

end GlobalTheory.LogPair
