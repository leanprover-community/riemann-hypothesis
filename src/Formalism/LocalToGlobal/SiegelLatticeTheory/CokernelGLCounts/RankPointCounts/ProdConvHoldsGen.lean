module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewHoldsGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem prodConv_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConv X u u' ψ :=
  prodConvNew_holds_gen X hb ψ hψ hs hloc u u'

theorem prodConv_holds {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) : ProdConv T.X u u' T.ψ :=
  prodConv_holds_gen T.X T.hb T.ψ T.ψ_char T.ψ_std T.locCompat u u'

theorem prodConvAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.ProdConvAll :=
  fun _ T u u' _ _ => prodConv_holds T u u'

theorem prodConv_onTied :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ hb X0 ψ hT
  exact prodConv_holds_gen X hb ψ hT.2.1 hT.2.2.1 hT.2.2.2.2.1 u u'

end Formalism.L2.SG.Pf.ProdConvCut2
