module

public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEq
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.companionLattice_adelicLattice_localization_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  first | exact @GlobalTheory.CompanLatAd.locP_companion_latAd | exact GlobalTheory.CompanLatAd.locP_companion_latAd | (intros; apply GlobalTheory.CompanLatAd.locP_companion_latAd <;> assumption)
