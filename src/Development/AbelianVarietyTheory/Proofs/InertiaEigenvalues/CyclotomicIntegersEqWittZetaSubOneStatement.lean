module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbWInjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOne
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS

theorem _root_.GlobalTheory.T.cyclotomic_integers_eq_witt_zeta_sub_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), 1 ≤ s → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ s) → ∀ t : OC l, (t : ℂ_[l]) = ((ζ - 1 : Om l) : ℂ_[l]) → (∀ r : Polynomial (WK K), r.natDegree < l ^ (s - 1) * (l - 1) → r.eval₂ (intToOC (unr K)) t = 0 → r = 0) ∧ (K.1 ≤ Ks K s → ∀ x : ↥(OL K), ∃ r : Polynomial (WK K), r.eval₂ (intToOC (unr K)) t = intToOC K x) := by
  first | exact @GlobalTheory.PrismS.Poly.main | exact GlobalTheory.PrismS.Poly.main | (intros; apply GlobalTheory.PrismS.Poly.main <;> assumption)
