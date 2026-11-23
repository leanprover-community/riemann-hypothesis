module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar GlobalTheory.CompanionTheory.Ar.TieArith ReciprocityTheory.ChartRestriction.G.AI.I4

section Comparison₂

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {K : Type} [Fintype K] {J : K → Type}

theorem exists_chart (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) :
    ∃ c : ∀ k, J k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  obtain ⟨c, hchart⟩ := h.cover (genCpt ξ)
  exact ⟨c, fun k ↦ (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)⟩

theorem ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ratioField y c = ⊤ := by
  have hne : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, u, hu, -, rfl⟩ := FracChart.exists_eq_div_adjoin X Ω ξ _ (seg y) c h hne a
  exact div_mem (adjoin_le_ratioField y c hg) (adjoin_le_ratioField y c hu)

theorem trdeg_eq_of_ringKrullDim [∀ k, Fintype (J k)] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hdim : ringKrullDim (MRing J ⧸ mCoordIdeal y) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    Algebra.trdeg ℤ Ω = d := by
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = Algebra.trdeg ℤ Ω := by
    rw [hb]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  have h2 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat =
      ((d + Fintype.card K : ℕ) : ℕ∞) := by
    generalize (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat = e at h1
    cases e using ENat.recTopCoe with
    | top => exact absurd h1 (by rw [top_add]; exact (ENat.natCast_ne_top _).symm)
    | coe e =>
      have h3 : e + 1 = d + 1 + Fintype.card K := by exact_mod_cast h1
      have h4 : e = d + Fintype.card K := by omega
      rw [h4]
  have h5 : Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal) = ((d + Fintype.card K : ℕ) : Cardinal) :=
    Cardinal.toENat_eq_natCast.mp h2
  rw [Nat.cast_add] at h5
  exact (Cardinal.add_nat_inj _).mp h5

end Comparison₂

theorem isArithVar_xb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d _ hT hA
  obtain ⟨c₀, hc₀⟩ := exists_chart 𝔐.ξ x₀ 𝔐.tie
  obtain ⟨cb, hcb⟩ := exists_chart 𝔐.ξ _ hT
  have hd : Algebra.trdeg ℤ Ω = d :=
    trdeg_eq_of_ringKrullDim x₀ c₀ hc₀ (ratioField_eq_top 𝔐.ξ x₀ 𝔐.tie c₀ hc₀) d hA.2.2.2
  obtain ⟨k₀⟩ := hA.1
  have hK : Nonempty (NonPluckerBlocks (blkF (CMType H) D.p D.q K₀)) := by
    refine ⟨⟨.inl k₀, fun r ↦ ?_⟩⟩
    unfold blkF
    split <;> simp
  exact isArithVar_of_ratioField_eq_top _ cb hcb (ratioField_eq_top 𝔐.ξ _ hT cb hcb) d hd

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase
