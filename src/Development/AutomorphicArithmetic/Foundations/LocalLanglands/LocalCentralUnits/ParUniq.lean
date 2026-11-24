module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.DetByType
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtEx
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameUniq
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.parUniq :
    UpperTheory.Zero.LLC.ParUniq := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz V hV
  obtain ⟨n, c⟩ := y
  have hn : 0 < n := hy.1
  have hcl : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL (k := HeightOneSpectrum.adicCompletion E w)) :=
    IrrGL.of_rep ⟨n, c⟩
  obtain ⟨D⟩ := UpperTheory.Zero.LLC.extEx E Ω A w h g i hi n hn
  obtain ⟨⟨R, hR⟩, hRT⟩ := UpperTheory.Zero.LLC.resEx E Ω A w h g i hi n hn D
  have hT := hRT R hR
  obtain ⟨τ, hτ, hinf⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A w h g i hi n hn c.rep).1
    (by rw [hcl]; exact hy) (by rw [hcl]; exact hdz)
  obtain ⟨hNex, -, hNchar, -⟩ := UpperTheory.Zero.LLC.nameLaws g n hn D.K hT.rank
  obtain ⟨θ, hθ, hθτ⟩ := hNex τ hτ
  have hIF : ∀ W : WD h, UpperTheory.Zero.LLC.Par a ⟨n, c⟩ W → UpperTheory.Zero.LLC.InFor g n R θ W :=
    fun W hW => (hW.type g i hi n hn D R hR θ hθ τ hτ hθτ c.rep hcl hinf).2
  obtain ⟨ω, -, hω, -⟩ := (UpperTheory.Zero.LLC.clBasic _ (⟨n, c⟩ : IrrGL (k := _))).1
  obtain ⟨-, hθu, hVu⟩ := UpperTheory.Zero.LLC.tameUniq E Ω A w h g n D.K R hT θ hθ V (hIF V hV)
  refine ⟨fun V' hV' => hVu V' hV.irr hV'.irr hV.tame hV'.tame (hIF V' hV')
    (fun s => by rw [hV.central ω hω s, hV'.central ω hω s]), ?_⟩
  rintro ⟨m, c'⟩ hy' hdz' hV'
  have hm : m = n := hV'.dim.symm.trans hV.dim
  subst m
  have hcl' : GlobalTheory.LocLanglands.cls c'.rep = (⟨n, c'⟩ : IrrGL (k := HeightOneSpectrum.adicCompletion E w)) :=
    IrrGL.of_rep ⟨n, c'⟩
  obtain ⟨τ', hτ', hinf'⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A w h g i hi n hn c'.rep).1
    (by rw [hcl']; exact hy') (by rw [hcl']; exact hdz')
  obtain ⟨θ', hθ', hθτ'⟩ := hNex τ' hτ'
  have hIF' : UpperTheory.Zero.LLC.InFor g n R θ' V :=
    (hV'.type g i hi n hn D R hR θ' hθ' τ' hτ' hθτ' c'.rep hcl' hinf').2
  obtain ⟨j, -, rfl⟩ := hθu θ' hIF'
  have hch : τ'.character = τ.character := hNchar τ τ' θ j hτ hτ' hθ hθτ hθτ'
  obtain ⟨ω', -, hω', -⟩ := (UpperTheory.Zero.LLC.clBasic _ (⟨n, c'⟩ : IrrGL (k := _))).1
  have hωω : ω' = ω := by
    ext z
    obtain ⟨s, rfl⟩ := ha.surj z
    exact (hV'.central ω' hω' s).symm.trans (hV.central ω hω s)
  subst ω'
  have hdet := UpperTheory.Zero.LLC.detByType E Ω A w h g i hi n hn c.rep c'.rep τ τ' ω hτ hch hinf hinf' hω hω'
  exact hcl'.symm.trans (hdet.trans hcl)
