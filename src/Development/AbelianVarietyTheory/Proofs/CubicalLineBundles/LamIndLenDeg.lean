module

public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibraryStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqParametersConstantStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormLetterLe
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamDegStLogOm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
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

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem GlobalTheory.LamF.lam_ind_len_deg :
    Formalism.L2.Pj.abelian₂.LamIndSt ∧ Formalism.L2.Pj.abelian₂.LamLenSt ∧
      ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D, Formalism.L2.Pj.abelian₂.LamDegSt Q.H large₂.logOm := by
  obtain ⟨hdeg, hind, hlen⟩ := GlobalTheory.T.cmLieStatements_iff_library
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  refine ⟨hind.1 GlobalTheory.LamF.Ind.lamInd, hlen.1 (GlobalTheory.LamF.lamLen GlobalTheory.thetaUnifAV_all hL), fun D Q hQ large₂ => ?_⟩
  obtain ⟨_, χ, hχ, h⟩ := GlobalTheory.T.exists_kronecker_cmLogPeriod_eq D Q hQ large₂
  rw [← h]
  exact (hdeg _ _ _).1 (GlobalTheory.LamF.lamDegSt_logOm GlobalTheory.thetaUnifAV_all hL _ Q.H χ hχ)
