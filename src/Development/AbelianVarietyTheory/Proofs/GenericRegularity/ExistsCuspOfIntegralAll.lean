module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHoldStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModularSectionOfIntegralGenericValueStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCuspFormOfIntegralOverDominantWeightStatement
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_cusp_of_integral_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ h : GenFrEx Xo c, ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (Z : Comp Xo c) (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F) (b : Om Z), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → b ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval (fun s => evC h Z (w s)) (cf i) * b ^ i = 0 → ∃ g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n), evC h Z g = b := by
  intro E _ _ _ H Dw l Xo c h r U hU a n N w hDom hw Z k m cf b hk hcf hb
  have hLaws : EvLaws Xo c ∧ IntDiagUnit Xo c ∧ GenFrEx Xo c ∧ ∀ h : GenFrEx Xo c, Atlas h :=
    GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨hEv, -, -, hAt⟩ := hLaws
  have hws : ∀ i, w i ∈ sec Xo c a n := fun i => (hw i).1
  obtain ⟨g, hg, hgZ, -, hgeq⟩ :=
    GlobalTheory.T.exists_modularSection_of_integral_genericValue E H Dw l Xo c hEv h (hAt h) a n N w hws Z k m cf b hcf hb
  exact ⟨g, GlobalTheory.T.isCuspForm_of_integral_over_dominantWeight E H Dw l Xo c hEv.test r U hU a n N w hDom hw k m cf hk hcf g hg hgeq, hgZ⟩

end GlobalTheory.Reg
