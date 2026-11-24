module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleOfCoproductCocycle
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

theorem _root_.GlobalTheory.T.stratifiedPhiModule_of_coproduct_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) → ∀ ε : Matrix (Fin d) (Fin d) En.Q.A, BK.hf En.inr bk.E ^ a • (A.map (BK.hf En.inl) * ε.map En.Q.D.φ) = BK.hf En.inl bk.E ^ a • (ε * A.map (BK.hf En.inr)) → (∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f) → ∃ S : Strat bk d, S.a = a ∧ S.A = A ∧ ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f := by
  first | exact @GlobalTheory.BSP.strat_of_envCocycle | exact GlobalTheory.BSP.strat_of_envCocycle | (intros; apply GlobalTheory.BSP.strat_of_envCocycle <;> assumption)
