module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndExp
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
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

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj CIndFrFix

def FrTruncFixBSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧ cc 0 = 0 ∧ (∀ m i j, cc m i j = cc m j i) ∧
      (∀ m (ℓ ℓ' : Lt1 Dw), ∑ i, ∑ j, cc m i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 →
        ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))

def HarmInvSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (cc : Fin C.d → Fin C.d → S), (∀ i j, cc i j = cc j i) →
    (∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, cc i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) →
    ∀ (k n D : ℕ) (f f' : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S),
    (∀ b, psJet D (f' b) = psJet D (f b * expP ((k : S) • diagL C.B H.w0 cc))) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      (∀ m ∈ P.support, m.degree ≤ D) → chartVal C k f' P = chartVal C k f P

theorem chartIndep2_verb (hTr : ChartIndepTruncSt) (hFix : FrTruncFixBSt) (hGerm : GermFixSt)
    (hInv : HarmInvSt) : ChartIndepSt2 := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C C' k n F f f' hf hf' a P hP

  have hD : ∀ m ∈ P.support, m.degree ≤ P.support.sup (fun m => m.degree) :=
    fun m hm => Finset.le_sup (f := fun m => m.degree) hm

  have step : ∀ (C₀ : ChartAt Xo c y) (f₀ : Fin n → MvPowerSeries (Fin 1 × Fin C₀.d) S),
      (∀ b, IsGerm y C₀.d C₀.x C₀.B.A.act C₀.e C₀.wP k (F b) (f₀ b)) →
      ∃ (C₁ : ChartAt Xo c y) (f₁ : Fin n → MvPowerSeries (Fin 1 × Fin C₁.d) S),
        FrTruncC y C₁ ∧ (∀ b, IsGerm y C₁.d C₁.x C₁.B.A.act C₁.e C₁.wP k (F b) (f₁ b)) ∧
        chartVal C₁ k f₁ P = chartVal C₀ k f₀ P := by
    intro C₀ f₀ hf₀
    obtain ⟨e', hfr, hrig, cc, hT1, -, hsym, hbal, hu⟩ := hFix E H Dw l Xo c hstar S y C₀
    choose f₁ hf₁ hj using fun b =>
      hGerm E H Dw l Xo c hstar S y C₀ e' hfr hrig cc hT1 hu k (F b) (f₀ b) (hf₀ b)
    exact ⟨{ C₀ with e := e', frame := hfr, rig0 := hrig }, f₁, hT1, hf₁,
      hInv E H Dw l Xo c hstar S y C₀ (cc (P.support.sup fun m => m.degree)) (hsym _) (hbal _) k n
        (P.support.sup fun m => m.degree) f₀ f₁ (fun b => hj b _) a P hP hD⟩
  obtain ⟨C₁, f₁, hC₁, hf₁, e₁⟩ := step C f hf
  obtain ⟨C₂, f₂, hC₂, hf₂, e₂⟩ := step C' f' hf'
  rw [← e₁, ← e₂]
  exact hTr E H Dw l Xo c hstar S y C₁ C₂ hC₁ hC₂ k n F f₁ f₂ hf₁ hf₂ a P hP

end Formalism.MainNotions.ModuliIntegralCharts.H1
