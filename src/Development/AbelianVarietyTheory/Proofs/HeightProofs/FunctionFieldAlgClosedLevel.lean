module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValuesStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefinedStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.FieldAlg

theorem recordField_le_of_pinField {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem fnAlgClosed_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ n : ℕ, 0 < n → CurveOver (hostOfRecord D) (FO D) n → ∀ j, InR D j → ∀ (l₂ : Level Q.H) (Xo₂ : Moduli (Q.Dw j) l₂) (c₂ : Coeff l₂), l₂.A = 1 → l₂.M ∣ n → c₂.F = Q.c.F → FnAlgClosed (Xo := Xo₂) (c := c₂) := by
  intro D Q hP hC n hn hcurve j hj l₂ Xo₂ c₂ hA hM hF
  obtain ⟨⟨ι, hι⟩, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 := GlobalTheory.RankOneDatum.exists_datum_rank_one D Q.H (Q.Dw j) (D.sp.W j) ι hι (by omega)
  have hle := recordField_le_of_pinField Q hP.2.2.1
  have hc : CurveOver Q.H (FO D) l₂.M := by
    have h0 : CurveOver Q.H (FO D) n := by rw [hC.1]; exact hcurve
    exact (GlobalTheory.T.cmCurveTorsion_definedOver_of_weberValues _ Q.H (FO D) n hn).2 _ hM h0
  refine GlobalTheory.T.coeffField_algClosed_functionField_of_torsionDefined _ Q.H (Q.Dw j) l₂ Xo₂ c₂ (by omega) hA (Or.inr (Or.inr ⟨by omega, h1⟩)) ?_
  intro τ hτ
  exact hc τ fun x hx => hτ x (by rw [hF]; exact hle hx)

end GlobalTheory.FinalJoin.FieldAlg
