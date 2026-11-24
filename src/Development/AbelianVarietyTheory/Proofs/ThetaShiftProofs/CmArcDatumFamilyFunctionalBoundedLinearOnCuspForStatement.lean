module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFamilyFunctionalBoundedLinearOnCuspFor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.cmArcDatumFamily_functional_bounded_linear_on_cuspForms :
    Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ)
    (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D),
    GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m →
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T j ka CR Tt cc K₁ d →
    ∃ φ : @LinearMap T.Q.c.F T.Q.c.F _ _ (RingHom.id T.Q.c.F) ((recB h).Cusp j ka) K₁
        ((recB h).acgC j ka).toAddCommMonoid _ ((recB h).modC j ka) _,
      (∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧
      @NumGood T.Q.c.F ((recB h).Cusp j ka) _ _ ((recB h).acgC j ka) ((recB h).modC j ka)
        {F | F ∈ (recB h).Mlat j ka} (fun σ F => (recB h).supN j ka σ F)
        (beOf D.host.E (nAt D j ka CR Tt cc) (absA (T.Q.Dw j) (wtA ka)))
        (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) K₁ _ _ _ φ := by
  exact @GlobalTheory.ArcCM.numGood_of_famQ
