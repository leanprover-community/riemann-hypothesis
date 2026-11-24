module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnArrowRealAverageFunctional
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.lastColumnArrow_realAverage_functional : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank)
      (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))), ∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.grid i D.R.m))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.grid i D.R.m)) (h : GA D (G.V (.grid (i + 1) D.R.m))) (v : VV ℂ (wt G (.grid i D.R.m))),
        ∫ k, W.kerA (.right i D.R.m : Arrow T) (W.fock (.chi i D.R.m) (movedVec t S d) Q)
            ((x : GA D (G.V (.grid i D.R.m))) * (k : GA D (G.V (.grid i D.R.m)))) h *
            Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) h⁻¹
            (fockComp W S.N.frC (.chi i D.R.m : Pair T) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  first | exact @GlobalTheory.LastColAvg.real_average | exact GlobalTheory.LastColAvg.real_average | (intros; apply GlobalTheory.LastColAvg.real_average <;> assumption)
