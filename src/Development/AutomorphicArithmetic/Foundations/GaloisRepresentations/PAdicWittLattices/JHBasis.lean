module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHBasis :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis := by
  classical
  intro k k' _ _ _ J e M N _ _ _ _ ψ hψ I c
  let T : (I →₀ k') ≃+ (J →₀ M) :=
    (Finsupp.mapRange.addEquiv e.repr.toAddEquiv).trans ((Finsupp.curryAddEquiv).symm.trans
      ((Finsupp.domCongr (Equiv.prodComm I J)).trans
        (Finsupp.curryAddEquiv.trans (Finsupp.mapRange.addEquiv c.repr.symm.toAddEquiv))))
  have hTs : ∀ (i : I) (a : k'),
      T (Finsupp.single i a) = Finsupp.mapRange (fun b : k => b • c i) (zero_smul k _) (e.repr a) := by
    intro i a
    ext j
    simp only [Finsupp.mapRange_apply]
    simp [T, Finsupp.curryAddEquiv]
    have h : ((Finsupp.equivMapDomain (Equiv.prodComm I J) (Finsupp.single i (e.repr a)).uncurry).curry j)
        = Finsupp.single i (e.repr a j) := by
      ext i'
      simp only [Finsupp.curry_apply, Finsupp.equivMapDomain_apply, Finsupp.uncurry_apply]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp_all
    rw [h, Finsupp.linearCombination_single]
  have hbc : ∀ f : J →₀ M, bcSum e ψ f = f.sum (fun j m => e j • ψ m) := by
    intro f
    simp [bcSum]; rfl
  let Φ : (I →₀ k') →ₗ[k'] N := Finsupp.linearCombination k' (fun i => ψ (c i))
  have key : ∀ g, Φ g = bcSum e ψ (T g) := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
    | single i a =>
      rw [hTs, hbc, Finsupp.sum_mapRange_index (by intro j; simp)]
      simp only [Φ, Finsupp.linearCombination_single]
      conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply]
      rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smulₛₗ, Algebra.smul_def, mul_comm, mul_smul]
  have hΦ : Function.Bijective Φ := by
    have h : (Φ : (I →₀ k') → N) = bcSum e ψ ∘ T := funext key
    rw [h]
    exact hψ.comp T.bijective
  let E := LinearEquiv.ofBijective Φ hΦ
  refine ⟨Module.Basis.ofRepr E.symm, fun i => ?_⟩
  rw [Module.Basis.coe_ofRepr]
  simp [E, Φ]
