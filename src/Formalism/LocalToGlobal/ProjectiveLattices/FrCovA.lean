module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.FrCov

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

section Comb

variable {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
  {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}

theorem eps_dual (ψ : S →+* T) (a : S) : spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

end Comb

variable (hS' : Out.SecBaseChangeAnySt) (hT : Out.SecTwistSt) {R T T' : Type} [CommRing R] [Algebra c.F R] [CommRing T]
  [Algebra c.F T] [CommRing T'] [Algebra c.F T']

abbrev Mx (Dw : Datum H) (T : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T

variable {y : FrPt Xo c R} {a : R →ₐ[c.F] T} {M M' N : Mx Dw T} {t t' r : T} {z z' : FrPt Xo c T} {w : FrPt Xo c T'}

include hS' hT

end Formalism.L2.Pj.FrCov
