module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.InterModel

variable {X Z : Scheme.{0}} {k : Type} [Field k] [Algebra k Γ(X, ⊤)]

variable (k) {ι : Type} [Fintype ι]

theorem radical_ker (f : Z ⟶ X) [QuasiCompact f] [IsReduced Z] : f.ker.radical = f.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine Ideal.IsRadical.radical fun a ⟨n, hn⟩ => ?_
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩

theorem interNumRed_eq_interNumOn (f : Z ⟶ X) [IsClosedImmersion f] [IsReduced Z]
    (C : Closeds X) (h : Set.range f = C) (L : ι → LB X) :
    interNumRed k C L = interNumOn k f L := by
  rw [interNumOn_eq_interNumSub, interNumRed_def, ← radical_ker f,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 2
  ext1
  rw [Scheme.Hom.support_ker, h, C.isClosed.closure_eq]

end GlobalTheory.InterModel
