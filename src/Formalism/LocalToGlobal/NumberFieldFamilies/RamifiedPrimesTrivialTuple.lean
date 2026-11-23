module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Fam.DivCQ

open Formalism.BasicNotions Formalism.L2.Host

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

structure ConjAt (D : D7) where
  M : ℕ → Type
  [instM : ∀ j, NormedAddCommGroup (M j)]
  [instMi : ∀ j, InnerProductSpace ℂ (M j)]
  [instMf : ∀ j, FiniteDimensional ℂ (M j)]
  T : ℕ → Type
  [instT : ∀ j, NormedAddCommGroup (T j)]
  [instTi : ∀ j, InnerProductSpace ℂ (T j)]
  [instTf : ∀ j, FiniteDimensional ℂ (T j)]
  th : ∀ j, T j →ₗ[ℂ] M j
  part : ∀ j, D.what₂.FT → Submodule ℂ (M j)

attribute [instance] ConjAt.instM ConjAt.instMi ConjAt.instMf ConjAt.instT ConjAt.instTi ConjAt.instTf


end Formalism.L2.Fam.DivCQ

end
