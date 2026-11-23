module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleLocalGlobalProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_tuple_local_global_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ X Y : Fin n → Fin M → AF F ⊗[F] E, projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ X : Fin n → Fin M → AF F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v) ∧ (∀ (Xinf : Fin n → Fin M → Ainf F ⊗[F] E) (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E), (∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) → ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v) ∧ ∀ (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact Cinf → (∀ v, IsCompact (Cv v)) → (∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) → IsCompact {X : Fin n → Fin M → AF F ⊗[F] E | projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Glue.glue_main | exact GlobalTheory.CompanionTheory.SW.Glue.glue_main | (intros; apply GlobalTheory.CompanionTheory.SW.Glue.glue_main <;> assumption)
