import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HarmonicChartValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecondCubicalLawIffClause
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NilpotentSubOrigin
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NablaPinCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames GlobalTheory.IndefiniteRowSideFullHecke.HarmonicChartValues GlobalTheory.GermSectionCompare
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {j : JetPts t.G x0 d}


theorem powFrame_isGen {T : Over X0} (z : T ⟶ t.G)
    (e : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame t.G t.PP.L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl


def zeroSec (t : SAB H X0) (k : ℤ) (T : Over X0) : LB.Sec (LPow t.G t.PP.L k T) := ⟨fun _ => 0, fun i j => by simp⟩




end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem starRing_eq (st : StarRing (𝓞 E)) (h : ∀ a : 𝓞 E, star a = H.bar a) : st = H.starRing := by
  obtain @⟨@⟨@⟨⟨s⟩, _⟩, _⟩, _⟩ := st
  obtain rfl : s = fun a => H.bar a := funext h
  rfl

section Chart

variable {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S}

variable (y) in

abbrev BarChart : Type := @ChartAt E _ _ _ H Dw l Xo c H.starRing S _ _ (ratAlg c S) y

abbrev Compat (C : BarChart y) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  FrTruncC y C

variable {d : ℕ} {j : JetPts Xo.univ.t.G y.x d} {e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j} {B : FBar H S d}
  {cf : Lt1 Dw → Fin d → S} {h : Germ.PS S 2 d} {eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j}



variable (j e B cf h eL) in

def SameData (C : BarChart y) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  ∃ wP hc hf hp hg hr, C = ⟨d, B, cf, chartEquiv _ y.x j, frameEquiv _ y.x j e, wP, h, hc, hf, hp, hg, hr⟩ ∧
    ∀ m, (eL m).IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL m)
      (eLG Xo.univ.t y.x d (chartEquiv _ y.x j) B.A.act (frameEquiv _ y.x j e) wP m)



def ComputesNat (C : BarChart y) (v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  (∀ (k : ℕ) (F : SecAt y k), ∃ f, Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
    ∀ (k : ℕ) (F : SecAt y k) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
      Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∀ α : Lt1 Dw →₀ ℕ, v k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)




end Chart

section Pin

variable (Xo c)

def IsNabCompat [StarRing (𝓞 E)] (nab : NabV Xo c) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) ∧
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S),
    ∃ C : ChartAt Xo c y, FrTruncC y C ∧
      (∀ (k : ℕ) (F : SecAt y k), ∃ f, Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
      ∀ (k : ℕ) (F : SecAt y k) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
          ∀ α : Lt1 Dw →₀ ℕ, nab y k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)

variable {Xo c}


def AgreeNat (nab nab' : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) (F : SecAt y k) (α : Lt1 Dw →₀ ℕ),
    nab y k F α = nab' y k F α







theorem AgreeNat.thExpr_eq {nab nab' : NabV Xo c} (h : AgreeNat nab nab') {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (F : Fin n → SecAt y ((l.M : ℤ) ^ 2)) :
    thExpr Xo c nab y P F = thExpr Xo c nab' y P F := by
  have key : ∀ (k : ℤ), 0 ≤ k → ∀ (F : SecAt y k) α, nab y k F α = nab' y k F α := by
    intro k hk
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact h S y k
  simp only [thExpr, key _ (sq_nonneg _)]



end Pin

end GlobalTheory.NablaPinCompare
