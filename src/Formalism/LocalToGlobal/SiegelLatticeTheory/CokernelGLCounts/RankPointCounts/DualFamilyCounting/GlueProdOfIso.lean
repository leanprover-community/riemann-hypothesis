module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPermOfMin
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibPNeZeroOfGenus
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibSEqSingleton
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExpOf
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

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem glueProd_of_iso (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp) :
    GlueProd := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos M hM Λ₀ hΛ₀ T hT
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs (nondegenerate_of hs hnd)
        hΛ₀.1 hΛ₀.2.1 }
  refine ⟨⟨genus_of_fib h1 h2 h6 hI hK hF hs hnd hUc hpos hM hΛ₀ hT, fun hg 𝔭 h𝔭 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hg h𝔭⟩, card_glue hK hF hUc hM hΛ₀ hΛ₀full hT⟩

end Formalism.L2.SG.Pf.G8

namespace Formalism.L2.SG.Pf.Cnt

theorem glueProd_of (h1 : JordanExists) (h2 : JordanInv) (h3 : JordanIsom) (h6 : GlueLoc) : GlueProd :=
  G8.glueProd_of_iso h1 h2 h6 (G8.isomFixOfExp_of h3)

end Formalism.L2.SG.Pf.Cnt
