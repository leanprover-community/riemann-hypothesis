module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def TanRel (U : UnifPre I D A G) (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) : Prop :=
  ∀ e : ℕ, ∃ ye : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
    ye ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left ∧
    ye ≫ (U.gt e).pG.left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ gm.b.left ∧
    ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ye)
      (LB.pullGen D.toPre.P.L _ _ (gm.s χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))))

def GtTan {D₀ : DegPre R} (gm : GtPt D₀ (epsR R)) : Prop :=
  ∃ o : GtPt D₀ (baseOver (Sp R)), o.IsZero ∧ GtPt.IsPull (redE R) gm o

abbrev toF (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : R →+* F :=
  (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))

def VecAt (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : epsR R ⟶ G)
    (yA : Sp (DualNumber F) ⟶ (TFK (R := R) F ⊗ A.A).left) : Prop :=
  yA ≫ (fst (TFK (R := R) F) A.A).left = spMap (algebraMap F (DualNumber F)) ∧
  yA ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = spMap (dualMap (toF R F)) ≫ y.left

def ArchF (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ (F : Type) [Field F] [CharZero F] [Algebra (FractionRing R) F] (e : F ≃+* ℂ) (N : NumD F) (ν : NumOf D F N) (g r m k : ℕ),
    1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D F (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∀ k₀ : F, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map (e : F →+* ℂ).toMonoidHom ζ)))
        (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = e k₀

def AllV (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G],
    Unif (IsLocalRing.maximalIdeal V) D A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif (IsLocalRing.maximalIdeal V) D A G, P U

def AllVC (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (_ : Unif (IsLocalRing.maximalIdeal V) D A G) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing V) C]
    {N : NumD C}, NumOf D.toPre C N → Prop) : Prop :=
  AllV fun {V} _ _ _ {D} {_} {_} _ _ U =>
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
      ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → P U ν

end GlobalTheory.MBLow

end
