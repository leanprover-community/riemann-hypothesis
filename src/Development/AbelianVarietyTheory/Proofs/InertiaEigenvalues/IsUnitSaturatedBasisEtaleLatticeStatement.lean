module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLattice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.isUnit_saturated_basis_etale_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  first | exact @GlobalTheory.EtaleLattice.isUnit_saturated_basis | exact GlobalTheory.EtaleLattice.isUnit_saturated_basis | (intros; apply GlobalTheory.EtaleLattice.isUnit_saturated_basis <;> assumption)
