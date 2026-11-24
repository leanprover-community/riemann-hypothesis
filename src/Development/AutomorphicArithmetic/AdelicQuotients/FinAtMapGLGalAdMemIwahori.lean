module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
public import GroundTheory.AutomorphicForms.AffineBruhat
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.AutomorphicArithmetic.AdelicQuotients.NormGaloisSmulAdeleComponentAtSmulPlace
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

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem val_lt_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one,
    Valued.toNormedField.norm_lt_one_iff]

private theorem val_le_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one,
    Valued.toNormedField.norm_le_one_iff]

private theorem val_eq_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ ‖y‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, val_le_iff', not_iff_not.1 (by
    rw [not_le, not_le]; exact val_lt_iff' w y : ¬ (1 ≤ ValuativeRel.valuation (w.adicCompletion E) y) ↔ ¬ (1 ≤ ‖y‖))]

theorem UpperTheory.finAt_mapGL_galAd_mem_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : AdelicGLn.AdelicGL E n),
        finAt w g ∈ GLnLocal.iwahori (w.adicCompletion E) n →
        finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) ∈ GLnLocal.iwahori ((σ • w).adicCompletion E) n := by
  intro F E _ _ _ _ _ σ n w g hg
  have key : ∀ i j, ‖finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) i j‖ = ‖finAt w g i j‖ :=
    fun i j => (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ (g i j)).1 w
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff _ n).1 hg
  refine (GLnLocal.mem_iwahori_iff _ n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [val_le_iff', key]; exact (val_le_iff' w _).1 (h1 i j)
  · rw [val_lt_iff', key]; exact (val_lt_iff' w _).1 (h2 i j hij)
  · rw [val_eq_iff', key]; exact (val_eq_iff' w _).1 (h3 i)
