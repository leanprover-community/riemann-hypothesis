module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParUniq
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem par_of_laws {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : LawsT a ha rc) {y : IrrGL (k := w.adicCompletion E)}
    (hc : y.IsCusp) (hG : Good y) (hd : DZ y) : Par a y (rc y) := by
  exact
    { irr := L.cusp y hc
      dim := L.dim y
      tame := L.depth y hG hd
      central ω hω := L.central y ω hG hω
      type := (typeIff E Ω A w h rc).1 L.type y }

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.recTUnique :
    UpperTheory.Zero.LLC.RecTUnique := by
  rintro E Ω _ _ _ _ _ A w h rc rc' ⟨a, ha, L⟩ ⟨a', ha', L'⟩ x hx
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain rfl : a' = a := (artEx E Ω A w h).unique ha' ha
  have key : ∀ y : IrrGL (k := w.adicCompletion E), y.IsCusp → GoodCusp y → rc y = rc' y := by
    intro y hc hg
    rcases id hg with h1 | ⟨⟨g, hgp, i, hi⟩, y₀, χ, hχ, hdz, rfl⟩
    · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ y).2.2.2.2.1 h1).2
      rw [L.one, L'.one]
    · haveI := hgp
      have ht := (clBasic _ y₀).2.1 χ hχ
      have hc₀ : y₀.IsCusp := ht.2.1.1 hc
      have hG : Good y₀ := ((goodSeg _).2.1 y₀ hc₀).2 (ht.2.2.1.1 hg)
      have e : rc' y₀ = rc y₀ :=
        (parUniq E Ω A w h _ ha g i hi y₀ hc₀ hdz (rc y₀) (par_of_laws L hc₀ hG hdz)).1 (rc' y₀)
          (par_of_laws L' hc₀ hG hdz)
      rw [L.twist _ _ _ hG, L'.twist _ _ _ hG, e, L.one, L'.one]
  obtain ⟨m, hm⟩ := Pr.exh _ x
  have hm' : IsL ((m.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
  rw [L.langlands _ x hm', L'.langlands _ x hm']
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [key Δ.first Δ.isCusp_first (((goodSeg _).1 _ x hm').1 hx Δ hΔ)]
