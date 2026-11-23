module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSplit

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcSplitS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcSplit
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def SplitOm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (r : ℕ)
    (P : Frame E n r) (MG : MeasG σ J r) (MW : MeasW σ J P)
    (hT : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j)
    (νH : Measure (Fin (r + 1 + r) → Fin n → AF F ⊗[F] E)) (Λ : Set (Fin n → E)),
    StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) → (gramE σ J (tupH P)).det ≠ 0 → 2 * (r + 1 + r) < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →
    Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → MG.IsTextNorm → MW.IsTextNorm →
    IsOmT F E σ n J ψ (gramE σ J (tupH P)) hT νH →
    IsCompatT F E σ n J (tupH P) MG.μG MW.μH νH →
    0 < MG.μGf (Kf σ J Λ) → MG.μGf (Kf σ J Λ) < ⊤ →
    ∃ a' : ℝ, 0 < a' ∧
      (AllSome (SdW F E σ n J (Ainf F) (psiInf F ψ) (r + 1 + r)) fun μinf =>
       AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) (r + 1 + r)) fun νinf =>
       AllSome (fun fibInf : HermR (Ainf F) σ (r + 1 + r) → Measure (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) =>
         IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
           {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf) fun fibInf =>
       ∀ f : HA (Ainf F) σ J → ENNReal, Measurable f →
         ∀ s : (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) → HA (Ainf F) σ J,
           (∀ y, (∃ g : HA (Ainf F) σ J, g • ratTup (Ainf F) (tupH P) = y) → s y • ratTup (Ainf F) (tupH P) = y) →
           ∫⁻ g, f g ∂MG.μGinf = ENNReal.ofReal a' *
             ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf F) σ J)) ∂MW.μHinf
               ∂(fibInf (hermOf (Ainf F) σ (gramE σ J (tupH P)) hT))) ∧
      (MG.μGf (Kf σ J Λ)).toReal * a' =
        (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal *
          ∏' v : HeightOneSpectrum (𝓞 F),
            (omAt σ J ψ v ((gramE σ J (tupH P)).map (inclR (Fv F v)))
              {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) (tupH P)}).toReal

end Formalism.L2.SG.Pf.NcSplitS
