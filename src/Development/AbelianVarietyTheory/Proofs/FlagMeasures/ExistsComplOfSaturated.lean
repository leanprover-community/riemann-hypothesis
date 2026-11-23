module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedHasComplement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem exists_compl_of_saturated {R V : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublatticeComplement.main
  | exact _root_.GlobalTheory.SaturatedSublatticeComplement.main
  | (apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublatticeComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublatticeComplement.main ..)

theorem saturatedFlag_splits : ∀ (E : Type) [Field E] [NumberField E] (n a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 E) (Fin n → E)), S 0 = ⊥ → Monotone S → (S (Fin.last a)).FG → (∀ i, ∀ y ∈ S (Fin.last a), y ∈ Submodule.span E (S i : Set (Fin n → E)) → y ∈ S i) → ∃ A : Fin a → Submodule (𝓞 E) (Fin n → E), ∀ i, A i ⊓ S i.castSucc = ⊥ ∧ A i ⊔ S i.castSucc = S i.succ := by
  intro E _ _ n a S _ hmono hfg hsat
  have key : ∀ i : Fin a, ∃ A : Submodule (𝓞 E) (Fin n → E),
      A ⊓ S i.castSucc = ⊥ ∧ A ⊔ S i.castSucc = S i.succ := by
    intro i
    have hle : S i.succ ≤ S (Fin.last a) := hmono (Fin.le_last _)
    refine exists_compl_of_saturated _ _ (hmono (Fin.castSucc_lt_succ).le)
      (Submodule.FG.of_le hfg hle) ?_
    intro r y hr hy hry
    apply hsat _ y (hle hy)
    have hr' : (algebraMap (𝓞 E) E r) ≠ 0 := by
      simpa using hr
    have : y = (algebraMap (𝓞 E) E r)⁻¹ • (r • y) := by
      rw [← algebraMap_smul E r y, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hry)
  choose A hA using key
  exact ⟨A, hA⟩

end GlobalTheory
