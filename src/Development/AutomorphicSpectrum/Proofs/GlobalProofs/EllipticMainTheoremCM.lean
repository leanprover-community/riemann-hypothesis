module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianizationEqOfForallAbRestrictEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAnalyticIsoOfIsAnalyticUniformization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqOnAlgebraicClosure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealLatticeToAddSubgroupEqIdealSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvSmulEqFinitePartInvSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAnalyticUniformizationOfIsAnalyticIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPointEqPointMapRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulQuotientInvMkEqMkIffMulEquiv
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField
open scoped nonZeroDivisors GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem ellipticMainTheoremCM : GlobalTheory.Published.EllipticMainTheoremCM := by
  classical
  intro K _ _ _ _ h2 Art hArt σ s hs X _ 𝔞 h𝔞 ξ hξ
  obtain ⟨Art₀, hArt₀, hlink⟩ := GlobalTheory.CompanionTheory.EllipticCM.exists_globalArtinMap_tied K h2
  have hEq : Art = Art₀ := MonoidHom.ext fun c =>
    GlobalTheory.CompanionTheory.GaloisAb.abelianization_eq_of_forall_abRestrict_eq K _ _ fun L h =>
      GlobalTheory.T.artin_map_abelian_unique K Art Art₀ hArt hArt₀ L h c
  subst hEq
  have hfound := hlink σ s hs
  let 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 𝔞 h𝔞
  have hf := GlobalTheory.CompanionTheory.EllipticCM.isAnalyticUniformization_of_isAnalyticIso h2 X 𝔞 h𝔞 ξ hξ
  obtain ⟨f', ⟨hf', hrel⟩, -⟩ :=
    GroundTheory.Global.Elliptic.main_theorem_complexMultiplication h2 σ s hfound 𝔞u hf
  have hid : ((s⁻¹ • 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • 𝔞 :=
    GlobalTheory.CompanionTheory.EllipticCM.inv_smul_eq_finitePart_inv_smul s 𝔞u
  rw [hid] at hf'
  have hex := GlobalTheory.CompanionTheory.EllipticUniformization.exists_analyticIso_of_isAnalyticUniformization _ _ f' hf'
  rw [GlobalTheory.CompanionTheory.EllipticDict.idealLattice_toAddSubgroup_eq_idealSub] at hex
  obtain ⟨ξ', hξ', hξf⟩ := hex
  refine GlobalTheory.EllipticCM.transports_of_exists h𝔞 rfl hξ' fun x => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ h𝔞 rfl (Submodule.Quotient.mk t))
  rw [← hy]
  have hq := (GlobalTheory.CompanionTheory.IdeleQuot.smulQuotient_inv_mk_eq_mk_iff_mulEquiv s 𝔞u t y).2 hy.symm
  have h3 := hrel t y hq
  rw [GlobalTheory.CompanionTheory.ConjPointDict.mapPoint_eq_pointMapRing, GlobalTheory.EllipticCM.torsionIncl_mk,
    GlobalTheory.EllipticCM.torsionIncl_mk, hξf, h3]
  rfl

end GlobalTheory.CompanionTheory.Hypotheses₂
