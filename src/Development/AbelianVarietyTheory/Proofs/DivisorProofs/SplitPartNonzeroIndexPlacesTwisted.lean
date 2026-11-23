module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
open GlobalTheory.CharRealise
open Formalism.DivisionValues

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)



theorem splitPartFace_baseLevel_indices_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw i p.P.A3.A.μ0 w = ((p.R.toRealDat.toCx (F2 p)).data (F2 p).cr false).Iw i p.P.A3.A.μ0 w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw i _ w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem splitPartFace_baseLevel_jw_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    jw ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).HT i p.P.A3.A.μ0) w ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).Tl i p.P.A3.A.μ0) =
      jw ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).HT i p.P.A3.A.μ0) w
        ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).Tl i p.P.A3.A.μ0) := by
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem w1_of_inW1_split_part (C CH : ℝ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (h : p.R.toRealDat.NonzeroIndexPlace (F2 p) w) :
    (p.R.toCx3 p.F).W1 p.F.cr (p.N C CH) w := by
  obtain ⟨w', hw', i, h⟩ := h
  refine ⟨i, ?_⟩
  rcases hw' with rfl | rfl
  · rcases h with h | h | h | h | h
    · exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · exact Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases h with h | h | h | h | h
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem tupTw_of_w1Row : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    SingleIndexPlacesAreTwisted p → p.R.toRealDat.tup_tw (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p h w hw
  exact h w (w1_of_inW1_split_part p 0 0 w hw)

end GlobalTheory.BigOn

end
