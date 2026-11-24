module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmE
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem relab_rt_iff (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt <;> assumption

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun z => Complex.conj_conj (τ z)

variable {σ : c.F →+* ℂ}



open Classical in
def nCol (U : Unf Xo c σ r) (n : ℕ) (k : U.Comp) (j : Fin r) : ℝ :=
  if (U.X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℝ) else -((n / 2 : ℕ) : ℝ)

end Formalism.L2.Pj
