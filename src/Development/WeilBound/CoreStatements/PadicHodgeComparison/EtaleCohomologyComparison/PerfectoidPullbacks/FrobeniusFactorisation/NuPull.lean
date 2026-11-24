module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicCompleteStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuGaloisCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuReductionCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuFrobeniusCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuGaloisCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuPullbackCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonFrobeniusCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonGaloisFixedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonPullbackCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonReductionCompatStatement
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem bW_red (r : Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)) :
    (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) := by apply GlobalTheory.T.witt_comparison_reduction_compat

theorem bW_phi (r : Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M n) :
    phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by apply GlobalTheory.T.witt_comparison_frobenius_compat

theorem bW_gal (r : Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ)
    (y : (HSW r M j).M n) : galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by apply GlobalTheory.T.witt_comparison_galois_fixed

theorem bW_pull (r : Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n) :
    pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by apply GlobalTheory.T.witt_comparison_pullback_compat

theorem nu_red (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j) :
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by apply GlobalTheory.T.teichmuller_nu_reduction_compat

theorem nu_phi (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by apply GlobalTheory.T.teichmuller_nu_frobenius_compat

theorem nu_gal (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K))
    (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) =
      galM r M σ hσ n j (Mid.nu r M n j hT x) := by apply GlobalTheory.T.teichmuller_nu_galois_compat

theorem nu_pull (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p)
    (n j : ℕ) (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by apply GlobalTheory.T.teichmuller_nu_pullback_compat

theorem mu_red (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) =
      Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) := by apply GlobalTheory.T.teichmuller_mu_reduction_compat

theorem mu_gal (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K))
    (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) =
      Mid.mu r M n j hT (galM r M σ hσ n j t) := by apply GlobalTheory.T.teichmuller_mu_galois_compat

theorem flatW (r : Res l K) : Module.Flat (WittVector l r.k) (AW r) := by apply GlobalTheory.T.witt_acris_flat

theorem adicA : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by apply GlobalTheory.T.acris_isAdicComplete_span_prime

end CrystallineSemistableComparison.Pb
