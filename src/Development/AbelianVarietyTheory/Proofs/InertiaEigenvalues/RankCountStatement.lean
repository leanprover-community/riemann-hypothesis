module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.exists_basis_and_equiv_fin_prod_of_basis : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  first | exact @GlobalTheory.Cyc.Decomp.rank_count | exact GlobalTheory.Cyc.Decomp.rank_count | (intros; apply GlobalTheory.Cyc.Decomp.rank_count <;> assumption)
