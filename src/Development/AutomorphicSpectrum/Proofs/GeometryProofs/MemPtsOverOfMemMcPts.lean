module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRing
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.OS

section Vals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hasVal_add {a : K → ℤ} {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y a s z w)
    (h' : Small.HasVal y a s' z w') : Small.HasVal y a (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', f', hg', hf', hd', e', hz0', ez'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := funext fun k => by
    have h1 := hd k
    have h2 := hd' k
    simp only [Pi.add_apply]
    omega
  refine ⟨dg + dh', dh + dh', g * f' + g' * f, f * f',
    FinRd.ValSub.mh_add (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hf') ?_,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hf hf', fun k => ?_, ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg' hf
  · have h1 := hd k
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_add (f := _), map_mul, e, e']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul, ez, ez']
    ring

theorem hasVal_zsmul {a : K → ℤ} {s : Ω} {w : 𝕜} (n : ℤ) (h : Small.HasVal y a s z w) :
    Small.HasVal y a (n • s) z (n • w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  refine ⟨dg, dh, MvPolynomial.C n * g, f, ?_, hf, hd, ?_, hz0, ?_⟩
  · intro m hm k
    rw [MvPolynomial.C_mul'] at hm
    exact hg m (MvPolynomial.support_smul hm) k
  · rw [map_mul, e, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]
  · rw [map_mul, ez, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]

theorem hasVal_zero_of {a : K → ℤ} {s : Ω} {w : 𝕜} (h : Small.HasVal y a s z w) :
    Small.HasVal y a (0 : Ω) z (0 : 𝕜) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  exact ⟨dg, dh, 0, f, FinRd.ValSub.mh_zero dg, hf, hd, by simp, hz0, by simp⟩

end Vals

section Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

end Coef

section Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Fin

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Arch

section ArchD

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

end ArchD

section Emb

end Emb

end GlobalTheory.CompanionTheory.Ar.Rec.OS

namespace GlobalTheory.CompanionTheory.Ar.Rec


end GlobalTheory.CompanionTheory.Ar.Rec
