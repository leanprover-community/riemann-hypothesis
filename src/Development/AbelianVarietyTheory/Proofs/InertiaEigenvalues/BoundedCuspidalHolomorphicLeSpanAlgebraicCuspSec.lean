module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalAtNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionFamilyNoCommonZeroLargeWeightStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanLeStatement
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

namespace GlobalTheory.SmallWtSpan

theorem holSub0_le_span_cuspSec : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  intro D T hT j hj σ hσ w hw hn P hP
  have hdom := dom_wtA w
  obtain ⟨b, m, N, t, hbm, ht, hunit, hprod⟩ := GlobalTheory.T.exists_section_family_no_common_zero_large_weight D T hT j hj σ hσ _ _ hdom
  have hP' := Submodule.mem_inf.mp hP
  have h2 := GlobalTheory.GlueSpan.span_of_products D T hT j hj σ hσ _ b _ m N t hdom hbm ht hunit P hP'.2
    (fun i => hprod P hP i)
  exact GlobalTheory.T.holomorphic_sections_span_le D T hT j hj σ hσ w hw hn (Submodule.mem_inf.mpr ⟨hP, h2⟩)

end GlobalTheory.SmallWtSpan
