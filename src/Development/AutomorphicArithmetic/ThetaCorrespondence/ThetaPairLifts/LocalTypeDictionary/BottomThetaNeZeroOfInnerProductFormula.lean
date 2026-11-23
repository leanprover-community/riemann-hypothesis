module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBottomBasisChange
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaLargeRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaSmallRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomMinorMatching
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotNeFormula

theorem bottomTheta_ne_zero_of_innerProduct_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  intro hPr hK hM hI hL hB hN hT
  have hLarge := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  have hSmall := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  have hMatch := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  have hBasis := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  unfold LNe at hL
  unfold BotSmall at hB
  unfold NormBig at hN
  unfold TriEx at hT
  unfold BotNe
  have hLevel := Model.gBig_and hL hB
  have hNorm := Model.gBig_and hN hT
  have hInputs := Model.gBig_and hLevel hNorm
  have hMatchBasis := Model.gBig_and hMatch hBasis
  have hSmallMatch := Model.gBig_and hSmall hMatchBasis
  have hFormulas := Model.gBig_and hLarge hSmallMatch
  have hAll := Model.gBig_and hInputs hFormulas
  apply BotConstPf.gBig_imp hAll
  intro D T Lc sc G μ₀ C x b hLc hData δ t0 Q P P' i j hbot
  have hLValues := hData.1.1.1
  have hTwistEmpty := hData.1.1.2.2.1
  have hNormFormula := hData.1.2.1
  have hTriangle := hData.1.2.2
  have hLargeFormula := hData.2.1
  have hSmallFormula := hData.2.2.1
  have hMinorMatch := hData.2.2.2.1
  have hBasisChange := hData.2.2.2.2
  have hmod : modT G μ₀ = SqNum.condE G.pl := by
    simp only [modT, hTwistEmpty, Finset.prod_empty, mul_one]
  rw [← hmod] at hbot
  obtain ⟨Λ, hΛ, hnz⟩ := (hLValues i j).1 μ₀
  have hh : (h0 D i j : ℤ) ≤ halfRank D i j :=
    Int.ofNat_le.mpr (squareBottomHalfRankSum_le_halfRank D i j)
  obtain ⟨Aa, hAa, hAn⟩ := hNormFormula δ t0 i j
  have hProd : (∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    have ⟨hs₁, hs₂⟩ := Finset.mem_Icc.mp hs
    exact hnz s hs₁ (hs₂.trans hh)
  have hP : P.norm ≠ 0 := fun hz =>
    mul_ne_zero hAa hProd ((hAn μ₀ Q P P' Λ hbot hΛ).symm.trans (Complex.ofReal_eq_zero.mpr hz))
  obtain ⟨h, Tt, hne⟩ := exists_coord_ne_of_norm_ne P hP
  constructor
  · exact ⟨h, Tt, hne⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Ker.Model.exists_stdChar D
  obtain ⟨W, hWψ⟩ := GlobalTheory.GridWeil.exists_weil hPr.weilRepresentationUnitaryPair D T Lc μ₀ hLc sc G ψ hψ
  have hψW : IsStdChar D W.ψ (-1) := hWψ ▸ hψ
  obtain ⟨A, A', WW, X₀, c₀, hX₀, hc₀⟩ := hTriangle W hψW i j
  obtain ⟨X, ζ, hX, hβ, -, hc⟩ := hBasisChange W hψW i j A A' WW X₀ c₀ hX₀ hc₀
  obtain ⟨Ω, -, HA⟩ := hLargeFormula W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', -, HB⟩ := hSmallFormula W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, -, HC⟩ := hMinorMatch W hψW i j A A' WW X (fun t => ζ t * c₀ t) hX hc
  obtain ⟨uA, -, -, -, HA⟩ := HA μ₀ Q P P' hbot
  obtain ⟨uB, -, -, -, HB⟩ := HB μ₀ Q P P' hbot
  have ea : P.a = A.rank := hbot.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hbot.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hbot.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have hd : P'.d = P.d := hbot.rank.2.2.2
  have ed' : P'.d = WW.rank := hd.trans ed
  obtain ⟨M, -, -, HC⟩ := HC μ₀ Q δ t0 P P' hbot ea ea' ed ed'
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  by_contra hz
  push Not at hz
  apply hne
  have e := HA ea ed h g hg Tt
  rw [HC g Tt] at e
  have hs : ∑ T', (M Tt T' : ℂ) * X.I' W.ψ W.θ μ₀ (GlobalTheory.BotFormula.minorF ea' ed' T') g = 0 := by
    apply Finset.sum_eq_zero
    intro T' _
    rw [HB ea' ed' (hd ▸ h) g hg' T', hz, mul_zero, mul_zero]
  rw [hs, mul_zero, mul_zero] at e
  simpa using e
end GlobalTheory.SqTop.BotNeFormula
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottomTheta_nonvanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  exact _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula
end
