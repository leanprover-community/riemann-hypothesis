module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGaloisEmbeddingExtension
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical


theorem _root_.GlobalTheory.T.local_galois_embedding_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  first | exact @GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | exact GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | (intros; apply GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous <;> assumption)
