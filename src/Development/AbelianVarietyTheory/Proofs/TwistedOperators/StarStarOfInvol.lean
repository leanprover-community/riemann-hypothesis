module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem star'_star'_of_invol {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {n : ℕ} (P : PPol σ n) (l : Fld P) : star' P (star' P l) = l := by
  have h : ((star' P : Fld P →+* Fld P).comp (star' P : Fld P →+* Fld P)) = RingHom.id (Fld P) := by
    refine AdjoinRoot.ringHom_ext (p := P.1) ?_ ?_
    · ext e
      change star' P (star' P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e
      rw [star'_algebraMap, star'_algebraMap, hσ]
    · change star' P (star' P (alpha P)) = alpha P
      rw [star'_alpha, map_inv₀, star'_alpha, inv_inv]
  exact RingHom.congr_fun h l

theorem trace_star'_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (l : Fld P), Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  intro F E _ _ _ σ hσ n P l
  let e₁ : E ≃+* E := RingEquiv.ofRingHom (σ : E →+* E) (σ : E →+* E) (RingHom.ext hσ) (RingHom.ext hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofRingHom (star' P : Fld P →+* Fld P) (star' P : Fld P →+* Fld P)
    (RingHom.ext (star'_star'_of_invol hσ P)) (RingHom.ext (star'_star'_of_invol hσ P))
  have he : RingHom.comp (algebraMap E (Fld P)) (e₁ : E →+* E) = RingHom.comp (e₂ : Fld P →+* Fld P) (algebraMap E (Fld P)) := by
    ext e
    exact (star'_algebraMap P e).symm
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  change _ = σ (Algebra.trace E (Fld P) (star' P l)) at h
  rw [h, hσ]

end GlobalTheory.TrEll
