module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedCuspidalHolomorphicLeSpanAlgebraicCuspSec
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.boundedCuspidalHolomorphic_le_span_algebraicCuspSections : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  first | exact @GlobalTheory.SmallWtSpan.holSub0_le_span_cuspSec | exact GlobalTheory.SmallWtSpan.holSub0_le_span_cuspSec | (intros; apply GlobalTheory.SmallWtSpan.holSub0_le_span_cuspSec <;> assumption)
