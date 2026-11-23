module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
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

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmInt_of_EZ {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hR : IsRowReps D F0 what₂)
    {Z : MatZ D} {F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')} (hz : F'.zt = F'.fl.z) (hZ : ZhatL (lf D F0) F' = Z)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z)) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : IsRowLat D F0 Λ) (hE : F' ∈ EZ (Tn u') F0 Λ Z) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') := by
  have hG := (((mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR Z F' hz hZ hP).2 Λ).mp ⟨hΛ, hE⟩
  by_contra hI
  rw [Formalism.L2.SG.Pf.Asm.glueSet_eq_empty (U := UPair D F0 F') hI] at hG
  exact hG

end Formalism.L2.SG.Pf.Cnt
