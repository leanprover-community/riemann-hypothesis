module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpTwOneNe
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PlainMono

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linked_single {ρ ρ' : IrrGL (k := k)} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (e : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := by
  subst e
  refine ⟨⟨Segment.ofFirst ρ hρ 2 two_pos, ?_⟩, ?_, ?_⟩
  · rw [Segment.carrier_single, Segment.carrier_single]
    ext z
    rw [Segment.mem_carrier]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact fun e => hne e.symm

theorem eq_single_of_len {Δ : Segment k} (h : Δ.len = 1) : Δ = Segment.single Δ.first Δ.isCusp_first :=
  Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, h])

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem ne_nu_one {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : UpperTheory.Zero.LLC.LawsT a ha rc) {ρ : IrrGL (k := w.adicCompletion E)}
    (hρ : ρ.IsCusp) : ρ ≠ ρ.nu 1 := by
  intro e0
  refine WD.lpTw_one_ne (rc ρ) (by rw [L.dim]; exact hρ.1) ?_
  calc (rc ρ).lpTw 1 = rc (ρ.nu ((1 : ℝ) : ℂ)) := (L.nu ρ 1).symm
    _ = rc ρ := by rw [Complex.ofReal_one, ← e0]

end GlobalTheory.PlainMono
