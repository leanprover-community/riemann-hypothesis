module

public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
public import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}


section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def Unf.ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

def Unf.toPj (U : Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

theorem rdU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (f : Formalism.L2.Pj.Rul Xo c) : rdU (Unf.ofPj U) f = Formalism.L2.Pj.rdU U f := rfl

theorem laU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    laU (Unf.ofPj U) a n k = Formalism.L2.Pj.laU U a n k := rfl

theorem isUnf_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : IsUnf (Unf.ofPj U) ↔ Formalism.L2.Pj.IsUnf U := rfl

theorem goodEmb_iff (σ : c.F →+* ℂ) : GoodEmb c σ ↔ Formalism.L2.Pj.GoodEmb c σ := rfl

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)

theorem cusp_ofPj (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (fun σ => Unf.ofPj (U σ)) a n = Formalism.L2.Pj.cusp Xo c U a n := rfl

theorem cuspMul_ofPj : CuspMul Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspMul Xo c U := rfl

theorem cuspFD_ofPj : CuspFD Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspFD Xo c U := rfl

theorem supDef_ofPj : SupDef Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.SupDef Xo c U := rfl

theorem regP_ofPj : regular₂ Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.regular₂ Xo c U := rfl

end Unif


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) (cls : ∀ (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr), Formalism.L2.Pj.IntFr Xo c T ι → Prop)



variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {r : ℕ}


end Formalism.L2.PjFree
