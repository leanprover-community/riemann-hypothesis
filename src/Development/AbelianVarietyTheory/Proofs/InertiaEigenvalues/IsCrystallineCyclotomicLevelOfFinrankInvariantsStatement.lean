module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  first | exact @GlobalTheory.Cyc.isCrys_Ks_of_finrank | exact GlobalTheory.Cyc.isCrys_Ks_of_finrank | (intros; apply GlobalTheory.Cyc.isCrys_Ks_of_finrank <;> assumption)
