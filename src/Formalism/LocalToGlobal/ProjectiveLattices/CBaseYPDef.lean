module

public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
public import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def colR (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (j : Fin r) : ℝ :=
  ‖dmin X.Gm x τ j.succ / dmin X.Gm x τ j.castSucc‖


def IsIdOrConj {σ σ' : c.F →+* ℂ} (φ : CAt σ →ₐ[c.F] CAt σ') : Prop :=
  (∀ z : CAt σ, toC (φ z) = toC z) ∨ ∀ z : CAt σ, toC (φ z) = starRingEnd ℂ (toC z)

def RdAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ))
    (q : Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ)) : Prop :=
  ∃ (y' : FrPt Xo c (CAt (goodOf c σ))) (φ : CAt σ →ₐ[c.F] CAt (goodOf c σ)),
    IsIdOrConj φ ∧ FrMap φ y y' ∧ FrBor q.2.2 ((U (goodOf c σ)).un q.1 q.2.1) y'



variable (Xo c) in
def CBaseEx (h : GenFrEx Xo c) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ y : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) y

def yPDef (h : GenFrEx Xo c) (hb : CBaseEx Xo c h) (Z : Comp Xo c) (P : Om Z →+* ℂ) : FrPt Xo c (CAt (sgOf P)) :=
  (hb Z P).choose

end Formalism.L2.Pj
