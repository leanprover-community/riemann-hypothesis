module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixed
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


open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (c : ι → W.EE) (w : ι → RW LL), (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ i, AI.gRW LL (g : GQ l) (w i) = w i) → (∀ i, w i = ∑ j, E.tie.ioE (M i j) * φRW LL (w j) + E.tie.ioE (c i)) → ∀ i, ∃ e : W.EE, E.tie.ioE e = w i := by
  first | exact @GlobalTheory.FrobDescent.mem_range_of_fixed | exact GlobalTheory.FrobDescent.mem_range_of_fixed | (intros; apply GlobalTheory.FrobDescent.mem_range_of_fixed <;> assumption)
