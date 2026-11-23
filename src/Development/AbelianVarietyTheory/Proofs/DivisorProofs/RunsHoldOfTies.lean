module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsConstantsIndexBoundHypothesesLiftWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
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

set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem runsHold_of_ties : ∃ CK x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G), CoreTies L EX J R → RunsOk fw r → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r := by
  obtain ⟨CK, x₁, H⟩ := GlobalTheory.T.exists_constants_indexBound_hypotheses_liftWeights
  refine ⟨CK, x₁, ?_⟩
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r hc ok hown hnum v h hinj
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnum
  have hl := ok.laws v
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) := by
    unfold ownAt
    split_ifs
    · exact hc.field₂
    · exact hc.field₁
  refine H D _ h hinj EX (ownAt D v) ?_ L Pm Tp hK h1 h2 h3 h4 h5 h6 hc.small
  refine GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws D J _ EX _ hl.j h hl.sh rfl hc.canon hF hc.halfEX ?_
  intro j hj n
  exact ⟨hl.lvA j hj n, hown v j n hj⟩

end GlobalTheory.BigOn
