module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

abbrev Comp : Type := irreducibleComponents (Xo.XF c)

variable {Xo c}

def genPt (Z : Comp Xo c) : Xo.XF c := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).genericPoint

abbrev kap (Z : Comp Xo c) : Type := (Xo.XF c).residueField (genPt Z)

abbrev strK : Xo.XF c ⟶ Sp c.F := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

def genSp (Z : Comp Xo c) : Spec ((Xo.XF c).residueField (genPt Z)) ⟶ Xo.XF c :=
  (Xo.XF c).fromSpecResidueField (genPt Z)

instance algKap (Z : Comp Xo c) : Algebra c.F (kap Z) :=
  (Spec.preimage (genSp Z ≫ strK)).hom.toAlgebra

def xGen (Z : Comp Xo c) : Sp (kap Z) ⟶ Xo.X :=
  genSp Z ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

abbrev FlagVar (Dw : Datum H) : Type := Σ τ : E →+* ℂ, {p : Fin (Dw.mult τ) × Fin (Dw.mult τ) // p.1 < p.2}

abbrev Om (Z : Comp Xo c) : Type := FractionRing (MvPolynomial (FlagVar Dw) (kap Z))

def genCoef (Z : Comp Xo c) (τ : E →+* ℂ) (i j : Fin (Dw.mult τ)) : Om Z :=
  if h : i < j then algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X ⟨τ, ⟨(i, j), h⟩⟩)
  else if i = j then 1 else 0

def IsGenFr (Z : Comp Xo c) (y : FrPt Xo c (Om Z)) : Prop :=
  y.x = spMap (algebraMap (kap Z) (Om Z)) ≫ xGen Z ∧
    ∃ y₀ : FrPt Xo c (kap Z), y₀.x = xGen Z ∧
      ∀ τ i, IsCombAt y.x (fun j => spMap (dualMap (algebraMap (kap Z) (Om Z))) ≫ y₀.u τ j)
        (genCoef Z τ i) (y.u τ i)


variable (Xo c) in
def GenFrEx : Prop := ∀ Z : Comp Xo c, ∃ y : FrPt Xo c (Om Z), IsGenFr Z y

def genFr (h : GenFrEx Xo c) (Z : Comp Xo c) : FrPt Xo c (Om Z) := (h Z).choose

theorem isGenFr_genFr (h : GenFrEx Xo c) (Z : Comp Xo c) : IsGenFr Z (genFr h Z) := (h Z).choose_spec

def evC (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : Om Z := evR Xo c f (genFr h Z)


variable (Xo c) in
def GenFromTest (h : GenFrEx Xo c) : Prop := ∀ Z : Comp Xo c,
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)

end Formalism.L2.Pj
