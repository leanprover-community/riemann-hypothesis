module

public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.DdREqDcris

theorem record_caseA : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
    Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1 := by
  intro D l _ K LL _ hb V _ _ _ _ _ ρ _ _ _ hc
  exact map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DdREqDcris
