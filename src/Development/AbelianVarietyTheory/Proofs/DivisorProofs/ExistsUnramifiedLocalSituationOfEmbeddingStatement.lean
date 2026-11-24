module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLocalSituationOfEmbedding
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

@[expose] public section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_unramifiedLocalSituation_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  first | exact @GlobalTheory.PlaceLetters.exists_place | exact GlobalTheory.PlaceLetters.exists_place | (intros; apply GlobalTheory.PlaceLetters.exists_place <;> assumption)
