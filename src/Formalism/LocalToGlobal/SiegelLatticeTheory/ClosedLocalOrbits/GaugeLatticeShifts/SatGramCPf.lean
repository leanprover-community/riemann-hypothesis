module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLStmt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoSEnd
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

theorem satGramC'_of (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC') (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') :
    SatGramC' := by
  intro D X Y u u' hI hA hF
  have h1 := Set.mem_insert (Y.tO u u').genSet {(Y.tO u u').ngSet, (Y.tO u u').degSet}
  have h2 : (Y.tO u u').ngSet ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  exact ⟨Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h1) (hR := hR D X Y u u' hI hA hF _ h1),
    Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h2) (hR := hR D X Y u u' hI hA hF _ h2)⟩

theorem leviOntoC_holds : LeviOntoC := fun _ _ Y u => Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u)

theorem normExpSatC'_of_acts (hN : NeatC) (hM : MassAC) (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC')
    (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') : NormExpSatC' :=
  normExpSatC'_of hN leviOntoC_holds hM (satGramC'_of hL hR)

end Formalism.L2.SG.NormCut
