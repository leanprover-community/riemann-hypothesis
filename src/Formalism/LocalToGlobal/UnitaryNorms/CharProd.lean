module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HeckeProd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host.HChar

variable {L : Type} [Field L] [NumberField L] (χ : HChar L)

theorem productRule : χ.ProductRule := hecke_product_rule L χ

theorem val_principal (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ v, v ∉ S → χ.UnrAt v) (k : Lˣ) :
    (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = (χ.inf k * ∏ v ∈ S, χ.locK v k)⁻¹ :=
  eq_inv_of_mul_eq_one_right (χ.productRule S hS k)

end Formalism.L2.Host.HChar
