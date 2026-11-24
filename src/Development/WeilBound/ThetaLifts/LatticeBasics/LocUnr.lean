module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

def LocUnrSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, Nonempty (E →ₐ[F] Fv F v) → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

def LocUnrInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, (∃ w, Formalism.UG.IsInertAt F E v w) → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

theorem locUnr_of (h₁ : LocUnrSplit) (h₂ : LocUnrInert) : LocUnr := fun F E _ _ _ _ _ σ B n Y r s hB hY χ hχ hr K e hK he v =>
  (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).elim (h₁ F E σ B n Y r s hB hY χ hχ hr K e hK he v)
    (h₂ F E σ B n Y r s hB hY χ hχ hr K e hK he v)

end GlobalTheory.ThK.Dbl

end
