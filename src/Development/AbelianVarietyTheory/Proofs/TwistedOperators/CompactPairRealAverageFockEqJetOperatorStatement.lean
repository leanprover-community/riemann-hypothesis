module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
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
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.compactPair_realAverage_fock_eq_jetOperator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ (b τ)) →
    ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2) →
      (∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))),
      ∀ (ℓ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] ℂ) (κ : Measure (GinfC (G.V (.grid i D.R.m)))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
        ∀ (k' : GA D (G.V (.grid (i + 1) D.R.m))), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) →
        ∀ v : VV ℂ (wt G (.grid i D.R.m)),
          ∫ k, realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) k' *
              ℓ (realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) k' Q) *
              Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
            Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) k'⁻¹
              (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
                (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) (nuEnd G (.chi i D.R.m : Pair T)) v)) := by
  first | exact @GlobalTheory.RowHoweAvg.real_average_jet | exact GlobalTheory.RowHoweAvg.real_average_jet | (intros; apply GlobalTheory.RowHoweAvg.real_average_jet <;> assumption)
