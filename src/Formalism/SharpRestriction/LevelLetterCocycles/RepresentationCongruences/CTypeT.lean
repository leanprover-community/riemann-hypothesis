module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCoreT
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitPi0InEE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem C_typeT (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (Si : Finset ℕ) (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O) (s₀ : ℕ)
    (hlt : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s bs)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1))
    (f : W.EE) (hf : InFr W c 1 (∏ s ∈ Si, ps W s ^ (match A.ty (c - (s : ZMod n)) with
        | .up bs => bs | _ => 0)) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hup : ∀ s < A.len c, s ∉ Si → ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ A.η) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    LiftsAtT W A F c b sol k₀ f (s₀ + A.σ PD.p) :=
  TC.C_typeT_of W A F c b sol k₀ hA hc hthick hcase hl hP9 hSec hGL hFL hArc hW₁ hW₂ hb Si hSi b₁ sol₁ hb₁ c₁ s₀
    hlt hpr f hf hdown hup

end Formalism.MainNotions.N.FrobeniusPowerSeries
