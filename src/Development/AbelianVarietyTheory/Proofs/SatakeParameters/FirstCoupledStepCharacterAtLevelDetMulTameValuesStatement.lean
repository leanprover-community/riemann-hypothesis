module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepCharacterAtLevelDetMulTameValues
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.firstCoupledStepCharacter_at_levelDet_mul_tameValues : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) = 1) := by
  first | exact @GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one | exact GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one | (intros; apply GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one <;> assumption)
