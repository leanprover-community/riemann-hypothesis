module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimeProperties
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

theorem _root_.GlobalTheory.T.ainf_envelope_mod_prime_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  first | exact @GlobalTheory.BSP.env_ainf_mod | exact GlobalTheory.BSP.env_ainf_mod | (intros; apply GlobalTheory.BSP.env_ainf_mod <;> assumption)
