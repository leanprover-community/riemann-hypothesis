module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomialStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpaceStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.FockChi

theorem fockIn_chi_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hc hδ ht i hi e0 he f hf
  have hcf := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ _ _ _ _ f hf
  obtain ⟨c, hc'⟩ := GlobalTheory.T.fockJets_unitVacuum_eq_unit_mul_periodJets W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.fr _) (N.fr _) (N.fr_on _ ⟨hi, rfl⟩) (N.fr_on _ ⟨by omega, rfl⟩)
    (W.cart_is _ ⟨hi, le_rfl⟩) (W.cart_is _ ⟨by omega, le_rfl⟩) δ t0 hc hδ ht e0 he _ hcf
  refine ⟨Units.map (starRingEnd ℂ).toMonoidHom c, fun k => ?_⟩
  have h2 := GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.frC (.grid (i + 1) D.R.m)) (N.frC (.grid i D.R.m)) f hf.1 hf.2.inf k 0
  have e1 : N.frC (.grid (i + 1) D.R.m) = fun τ => (N.fr (.grid (i + 1) D.R.m)).1.map (tauE D τ) := rfl
  have e2 : N.frC (.grid i D.R.m) = fun τ => (N.fr (.grid i D.R.m)).1.map (tauE D τ) := rfl
  show pureTensorO _ _ _ _ _ _ _ _ f _ 0 = _
  rw [h2, e1, e2, hc' k, map_mul]
  rfl

end GlobalTheory.FunObj.FockChi
