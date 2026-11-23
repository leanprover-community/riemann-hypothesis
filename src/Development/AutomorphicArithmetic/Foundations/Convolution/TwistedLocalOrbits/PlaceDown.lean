module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearDown
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)

theorem UpperTheory.ConvolutionTheory.Loc.placeDown :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
      (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
        [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
        (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))), mE.IsHaarMeasure → mF.IsHaarMeasure →
      ∃ ρ : ValueGroupWithZero (w.1.adicCompletion E), 0 < ρ ∧ ∀ φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)), Function.support φ ⊆ ball n ρ →
        ∃ f ∈ SB (GL (Fin n) (v.adicCompletion F)), PositivityTheory.Rg.Tf.Geo.Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF 1 (fun g => φ (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g)) f := by
  intro F E _ _ _ _ _ _ σ hσ v w hw n _ _ _ _ mE mF hE hF
  obtain ⟨iA, iV, iF, iG, s, hs, hrk, hinc, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨hH, hM⟩ := UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E σ hσ v w hw s hs hrk hinc hgal n mE mF hE hF
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨ρ, hρ, h⟩ := UpperTheory.ConvolutionTheory.Loc.nearDown (v.adicCompletion F) (w.1.adicCompletion E) s hs n _ mF hH hF
  refine ⟨ρ, hρ, fun φ hφ hsup => ?_⟩
  obtain ⟨f, hf, hm⟩ := h φ hφ hsup
  exact ⟨f, hf, hM φ hφ f hf hm⟩
