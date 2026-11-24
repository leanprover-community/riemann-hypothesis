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
import Mathlib.Tactic.NormNum.RealSqrt
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

abbrev LevelMod (Dw : Datum H) (l : Level H) : Type :=
  Dw.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))

abbrev LevelAut (Dw : Datum H) (l : Level H) : Type := LevelMod Dw l ≃ₗ[𝓞 E] LevelMod Dw l

def IsRigCubIso {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (ν : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull ν.φ)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (ν.cm.thetaPull t.PP.L t.cub.t)

def MovesLevel (Xo : Moduli Dw l) (g : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) : Prop :=
  ρ ≫ Xo.s = Xo.s ∧
    (∀ a b : Dw.La, Submodule.Quotient.mk b = g (Submodule.Quotient.mk a) →
      (Xo.univ.eta b).left ≫ ν.φ = ρ ≫ (Xo.univ.eta a).left) ∧
    ∀ a : Dw.La, (Xo.univ.etaA a).left ≫ ν.φ = ρ ≫ (Xo.univ.etaA a).left

variable {Xo : Moduli Dw l} {c : Coeff l}

def Carries {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.φ))
    {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ≫ ρ ∧
    (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧
    ∃ pm : Gx y.x ⟶ Gx y'.x,
      pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ ∧
      pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
      ∀ (i i' : Fin 1 → Xo.univ.t.PP.L.ι) (V : (Gx y.x).Opens)
        (h : V ≤ (PPx y.x).U i) (h' : V ≤ pm ⁻¹ᵁ (PPx y'.x).U i')
        (hw : V ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
          (LB.div (Xo.univ.t.PP.L.pull ν.φ) Xo.univ.t.PP.L).U (fun _ => i' 0, i 0)),
        (pm.appLE _ V h').hom (y'.s.f i') =
          ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE _ V hw).hom (w.s (fun _ => i' 0, i 0)).val *
            resG (Gx y.x) h (y.s.f i)

def LevelMove (g : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.φ)),
    MovesLevel Xo g ρ ν ∧ IsRigCubIso ν w ∧ Carries ν w y y'

abbrev RelFam (Xo : Moduli Dw l) (c : Coeff l) (G : Type) : Type 1 :=
  G → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → FrPt Xo c S → Prop

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

def Total : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ y', R g S y y'

def Functional : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (y y₁ y₂ : FrPt Xo c S), R g S y y₁ → R g S y y₂ → y₁ = y₂

def Unital : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), R 1 S y y

def Multiplicative' : Prop :=
  ∀ (g h : G) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S),
    R g S y y' → R h S y' y'' → R (g * h) S y y''

def Natural : Prop :=
  ∀ (g : G) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S')
    (y y' : FrPt Xo c S) (z z' : FrPt Xo c S'), FrMap φ y z → R g S y y' → R g S' z z' → FrMap φ y' z'

def Triangular : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' z z' : FrPt Xo c S),
    FrBor t y z → R g S y y' → R g S z z' → FrBor t y' z'

def ActionLaws : Prop :=
  Total R ∧ Functional R ∧ Unital R ∧ Multiplicative' R ∧ Natural R ∧ Triangular R

variable {R}

end Laws

end General

variable {D : D7}

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms
