module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardPiOfUnique
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BcPFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFull
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

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem locFullC_holds : LocFullC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT p M hM
  exact Formalism.L2.SG.Pf.LocalDenominators.exists_isLattice_eq_localLattice Zd p M hM.1.1.1.1 hM.1.1.1.2.1

theorem patchC_holds : PatchC Zd u u' F0 what₂ := patchC_of_full Zd (locFullC_holds Zd u u' F0 what₂)

variable {Zd u u' F0 what₂}

theorem frGlob_of_fstar (hA : FStarC Zd u u' F0 what₂) : Formalism.L2.SG.Pf.PCount.FrGlob Zd u u' F0 what₂ :=
  frGlob_of Zd hA (patchC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching
