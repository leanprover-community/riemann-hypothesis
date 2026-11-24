module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.PrincipalCongruenceMemLevel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLatStepPf
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

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf

theorem noCocompactC_holds : NOCocompactC := UnipB.noCocompactC_of UnipB.latStepC_holds

theorem noCofinite_holds {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : NOCofinite X u := by
  obtain ⟨C, hC, hcov⟩ := noCocompactC_holds D X u
  have hfin := (haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (UnipB.ninf_closed X u) (X.muN u)
    (X.muN_haar u)).2.1
  exact ⟨C, hC.isClosed.measurableSet, hfin C hC, hcov⟩

theorem noCofiniteC_holds : NOCofiniteC := fun _ X u => noCofinite_holds X u

end Formalism.L2.SG.Pf
