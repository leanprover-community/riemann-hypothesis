module

public import Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfB
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
public import Mathlib.RingTheory.NoetherNormalization
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

namespace LateralTheory.E.E4

def LeafNoetherDim : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] B),
  Function.Injective g → g.Finite → s = 1

theorem LeafNoetherCurve_of (hD : LeafNoetherDim) : LeafNoetherCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨s, g, hg, hf⟩ := exists_finite_inj_algHom_of_fg k B
  obtain rfl := hD k B hB s g hg hf
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    (MvPolynomial.finSuccEquiv k 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))
  refine ⟨g.comp e.symm.toAlgHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem LeafUnitsFG_of_dim (hD : LeafNoetherDim) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_leaves (LeafNoetherCurve_of hD) hV

end LateralTheory.E.E4
