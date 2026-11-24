module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BChartEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DCoord
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

theorem blChart : BlowUpChart₂ := by
  intro R _ Z W _ π hπ D c
  set φ := MvPolynomial.eval₂Hom (secMap (p1 Z) c.h1).toRingHom c.s with hφ
  have hs : (fun k => φ (MvPolynomial.X k)) = c.s := by
    funext k
    simp [hφ]
  have hflat : φ.Flat := by
    have he := dCoord R Z D c
    algebraize [φ]
    exact Algebra.Smooth.flat _ _
  haveI : QuasiCompact (Over.Hom.left (dg Z)) := by
    change QuasiCompact (pullback.diagonal (Over.hom Z))
    infer_instance
  have hI : (Scheme.Hom.ker (Over.Hom.left (dg Z))).ideal ⟨c.N, c.aff⟩
      = Ideal.span (Set.range fun k => φ (MvPolynomial.X k)) := by
    rw [Scheme.Hom.ker_apply, hs, Scheme.Hom.app_eq_appLE]
    exact c.ker
  have key := bChartEx R π _ hπ ⟨c.N, c.aff⟩ D (Sec Z c.U) φ hflat hI
  rw [hs] at key
  exact key

end UpperTheory.Gal.KunnethLefschetz.G
