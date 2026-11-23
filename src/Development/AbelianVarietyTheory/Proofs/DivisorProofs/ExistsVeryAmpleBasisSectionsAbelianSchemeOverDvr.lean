module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfLinearSpanCombinationStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_veryAmpleBy_basis_of_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  intro W _ _ _ G _ hG M m t₀ hM hv
  have hflat : Flat G.hom := by
    haveI := hG.smooth
    infer_instance
  obtain ⟨n, t, ht⟩ := GlobalTheory.T.exists_basis_lineBundleSections_projective_over_dvr W G.left G.hom M hflat ⟨M, hM, m, t₀, hv⟩ hM
  have hne : Nonempty G.left := by
    obtain ⟨x⟩ : Nonempty (Sp W) := inferInstance
    exact ⟨(η[G]).left x⟩
  obtain ⟨x⟩ := hne
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv.1.ge (Set.mem_univ x))
  have hn : n ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc, -⟩ := ht (t₀ i₀)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hc
    rw [hc] at hi₀
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi₀
    have hk' : x ∈ G.left.basicOpen (0 : Γ(G.left, M.U k)) := hk
    rw [Scheme.basicOpen_zero] at hk'
    exact hk'
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  choose a ha using fun i => (ht (t₀ i)).exists
  exact ⟨N, t, GlobalTheory.T.isVeryAmpleBySections_of_linear_span_combination W G.left G.hom M m N t₀ t a hM hv ha, ht⟩
