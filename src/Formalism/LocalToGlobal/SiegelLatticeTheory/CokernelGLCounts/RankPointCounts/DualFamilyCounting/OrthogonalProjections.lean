module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization
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
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormMemOfDual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.OrthogonalProjections

theorem fibre_counting_holds : FibCount := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne
  have oUW : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => h_UW hx hy
  have oWU : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := fun x hx y hy => h_WU hs hx hy
  have hO := projOnto_of summand_localization riesz_hermitian_holds
  have hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hcU M T 𝔭 Λ := fun Λ hΛ =>
    { iU := projection_into_holds K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      iW := projection_into_holds K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1
        hΛ.2.2.2
      oU := hO K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      oW := hO K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.2
      cU := hΛ.2.2.1
      cW := hΛ.2.2.2 }
  obtain ⟨⟨⟨Λ₀, h0⟩⟩, -⟩ := Nat.card_ne_zero.mp hne
  exact card_eq hs h𝔭 hM hT hgood h0

end Formalism.L2.SG.Pf.Cnt
