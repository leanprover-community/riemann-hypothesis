module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace GlobalTheory.DeltaPinTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem noDelta_phiPin (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (noDelta Xo c nab m n).PhiPin (fun _ => 1) 1 (fun _ => 0) := by
  haveI hs : Subsingleton (LaJ Xo c (noDelta Xo c nab m n)) := by
    apply Submodule.Quotient.subsingleton_iff.2
    show Ideal.map _ ⊤ • ⊤ = ⊤
    rw [Ideal.map_top, Submodule.top_smul]
  refine ⟨fun _ _ _ => rfl, fun _ _ => Subsingleton.elim _ _, fun _ _ _ _ => by simp, rfl,
    Subsingleton.elim _ _, fun q => ?_⟩
  haveI : Unique (Fin n → LaJ Xo c (noDelta Xo c nab m n)) := uniqueOfSubsingleton (fun _ => 0)
  rw [finsum_unique]
  have hz : ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) = 1 := by
    have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    apply Subtype.ext
    rw [Nat.div_one]
    exact (Complex.isPrimitiveRoot_exp _ h0).pow_eq_one
  show (noDelta Xo c nab m n).eF 1 = (noDelta Xo c nab m n).eF 1 * ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) ^ _
  rw [hz]
  exact ((congrArg _ (one_zpow _)).trans (mul_one _)).symm

end GlobalTheory.DeltaPinTest
